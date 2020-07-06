{-# language OverloadedLists, OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language TypeApplications #-}
module Main where

import Bound.Scope (toScope)
import Bound.Var (Var(..))
import Control.Lens.Setter ((.~))
import Control.Monad.Except (runExceptT)
import Control.Monad.State.Strict (evalState, evalStateT)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Function ((&))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Text.IO as Text
import Data.Void (Void, absurd)
import Test.Hspec

import Check.Datatype (checkADT)
import Check.Entailment
  ( SMeta(..), Theory(..)
  , composeSSubs
  , globalTheory
  , freshSMeta, simplify, solve
  )
import Check.Function (checkFunction)
import Check.TCState (emptyTCState)
import qualified Codegen.C as C
import qualified Compile
import Error.TypeError (TypeError(..))
import Size ((.@), Size, sizeConstraintFor)
import qualified Size (Size(..), pattern Var)
import qualified Size.Builtins as Size (builtins)
import IR (Constraint(..), Kind(..))
import qualified IR
import Syntax (Index(..), Type(..), pattern TypeM, TMeta(..), Span(Unknown))
import qualified Syntax

import Test.Parser (parserTests)

main :: IO ()
main =
  hspec $ do
    parserTests
    describe "sizeConstraintFor" $ do
      it "*" $
        sizeConstraintFor @Void KType `shouldBe` CSized (TVar $ B ())
      it "* -> *" $
        sizeConstraintFor @Void (KArr KType KType) `shouldBe`
        CForall Nothing KType
          (CImplies
             (CSized (TVar $ B ()))
             (CSized $
              TApp Unknown
                (TVar $ F $ B ())
                (TVar $ B ())
             )
          )
      it "* -> * -> *" $
        sizeConstraintFor @Void (KArr KType $ KArr KType KType) `shouldBe`
        CForall Nothing KType
          (CImplies
             (CSized $ TVar $ B ())
             (CForall Nothing KType . CImplies (CSized $ TVar $ B ()) $
              CSized $
              TApp Unknown
                (TApp Unknown
                   (TVar $ F $ F $ B ())
                   (TVar $ F $ B ())
                )
                (TVar $ B ())
             )
          )
      it "* -> (* -> *) -> *" $
        sizeConstraintFor @Void (KArr KType $ KArr (KArr KType KType) KType) `shouldBe`
        -- forall x : Type
        CForall Nothing KType
          -- Sized x =>
          (CImplies (CSized $ TVar $ B ()) $
           -- forall y : Type -> Type.
           CForall Nothing (KArr KType KType) .
           -- (forall z : Type. Sized z => Sized (y z)) =>
           CImplies
             (CForall Nothing KType $
              CImplies
                (CSized $ TVar $ B ())
                (CSized $ TApp Unknown (TVar $ F $ B ()) (TVar $ B ()))
             ) $
           -- Sized (#0 x y)
           CSized $
           TApp Unknown
             (TApp Unknown
               (TVar $ F $ F $ B ())
               (TVar $ F $ B ())
             )
             (TVar $ B ())
          )
    describe "entailment" $ do
      it "simplify { (4, Sized I32) } (d0 : Sized I32) ==> [d0 := 4]" $ do
        let
          theory :: Theory (Either TMeta Void)
          theory =
            Theory
            { _thGlobal =
              [ (CSized $ TInt32 Unknown, Size.Word 4)
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState emptyTCState . runExceptT $ do
            m <- freshSMeta
            (,) m <$> simplify mempty Syntax.voidSpan absurd absurd theory (m, CSized $ TInt32 Unknown)
        case e_res of
          Left{} -> expectationFailure "expected success, got error"
          Right (d0, res) -> res `shouldBe` ([], [(d0, Size.Word 4 :: Size (Either SMeta Void))])

      it "solve $ simplify { (4, Sized I32), (\\x -> x + x, forall a. Sized a => Sized (Pair a)) } (d0 : Sized (Pair I32)) ==> [d0 := 8]" $ do
        let
          kindScope =
            [ ("Pair", KArr KType $ KArr KType KType)
            ]

          theory :: Theory (Either TMeta Void)
          theory =
            Theory
            { _thGlobal =
              [ (CSized $ TInt32 Unknown, Size.Word 4)
              , ( CForall (Just "a") KType $
                  CImplies
                    (CSized $ TVar $ B ())
                    (CSized $ TApp Unknown (TName Unknown "Pair") (TVar $ B ()))
                , Size.Lam . toScope $ Size.Plus (Size.Var $ B ()) (Size.Var $ B ())
                )
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (assumes, sols) <-
              fmap (fromMaybe ([], mempty)) . runMaybeT $
              simplify
                kindScope
                Syntax.voidSpan
                absurd
                absurd
                theory
                (m, CSized $ TApp Unknown (TName Unknown "Pair") (TInt32 Unknown))
            (assumes', sols') <- solve kindScope Syntax.voidSpan absurd absurd theory assumes
            pure (m, (assumes', composeSSubs sols' sols))
        case e_res of
          Left err -> expectationFailure $ "expected success, got error: " <> show err
          Right (d0, (assumes, sols)) ->
            Map.lookup d0 sols `shouldBe` Just (Size.Word 8 :: Size (Either SMeta Void))

      it "solve $ simplify { (\\x -> x + x, forall a. Sized a => Sized (Pair a)) } (d0 : Sized (Pair I32)) ==> cannot deduce  Sized I32" $ do
        let
          kindScope =
            [ ("Pair", KArr KType $ KArr KType KType)
            ]

          theory :: Theory (Either TMeta Void)
          theory =
            Theory
            { _thGlobal =
              [ ( CForall (Just "a") KType $
                  CImplies
                    (CSized $ TVar $ B ())
                    (CSized $ TApp Unknown (TName Unknown "Pair") (TVar $ B ()))
                , Size.Lam . toScope $ Size.Plus (Size.Var $ B ()) (Size.Var $ B ())
                )
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (assumes, sols) <-
              fmap (fromMaybe ([], mempty)) . runMaybeT $
              simplify
                kindScope
                Syntax.voidSpan
                absurd
                absurd
                theory
                (m, CSized $ TApp Unknown (TName Unknown "Pair") (TInt32 Unknown))
            (assumes', sols') <- solve kindScope Syntax.voidSpan absurd absurd theory assumes
            pure (m, (assumes', composeSSubs sols' sols))
        case e_res of
          Left err -> err `shouldBe` CouldNotDeduce (CSized $ TInt32 Unknown)
          Right{} -> expectationFailure "expected failure, got success"

      it "solve $ simplify { (\\x -> x + x, forall x. Sized x => Sized (Pair x)) } (d0 : forall a. Sized (Pair a) => Sized a) ==> cannot deduce   Sized a" $ do
        let
          theory :: Theory (Either TMeta Void)
          theory =
            Theory
            { _thGlobal =
              [ ( CForall (Just "x") KType $
                  CImplies
                    (CSized $ TVar $ B ())
                    (CSized $ TApp Unknown (TName Unknown "Pair") (TVar $ B ()))
                , Size.Lam . toScope $ Size.Plus (Size.Var $ B ()) (Size.Var $ B ())
                )
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (assumes, sols) <-
              fmap (fromMaybe ([], mempty)) . runMaybeT $
              simplify mempty Syntax.voidSpan absurd absurd theory
                ( m
                , CForall (Just "a") KType $
                  CImplies
                    (CSized $ TApp Unknown (TName Unknown "Pair") (TVar $ B ()))
                    (CSized $ TVar $ B ())
                )
            (assumes', sols') <- solve @_ @Void mempty Syntax.voidSpan absurd absurd theory assumes
            pure (m, (assumes', composeSSubs sols' sols))
        case e_res of
          Left err -> err `shouldBe` CouldNotDeduce (CSized $ TVar $ Right "a")
          Right res -> expectationFailure $ "expected error, got success: " <> show res

    describe "typechecking" $ do
      it "id<A>(x : A) -> A" $ do
        let
          input =
            Syntax.Function
            { Syntax.funcName = "id"
            , Syntax.funcTyArgs = ["A"]
            , Syntax.funcArgs = [("x", TVar . B $ Index Unknown 0)]
            , Syntax.funcRetTy = TVar . B $ Index Unknown 0
            , Syntax.funcBody = Syntax.Var . B $ Index Unknown 0
            }
          output =
            IR.Function
            { IR.funcName = "id"
            , IR.funcTyArgs = [("A", KType)]
            , IR.funcConstraints = [CSized $ TVar . B $ Index Unknown 0]
            , IR.funcArgs = [("x", TVar . B $ Index Unknown 0)]
            , IR.funcRetTy = TVar . B $ Index Unknown 0
            , IR.funcBody = IR.Var . B $ Index Unknown 0
            }
        evalStateT (checkFunction mempty mempty mempty mempty mempty input) (emptyTCState @Void) `shouldBe`
          Right output
      it "five() -> int32" $ do
        let
          input =
            Syntax.Function
            { Syntax.funcName = "five"
            , Syntax.funcTyArgs = []
            , Syntax.funcArgs = []
            , Syntax.funcRetTy = TInt32 Unknown
            , Syntax.funcBody = Syntax.Number Unknown 5
            }
          output =
            IR.Function
            { IR.funcName = "five"
            , IR.funcTyArgs = []
            , IR.funcConstraints = []
            , IR.funcArgs = []
            , IR.funcRetTy = TInt32 Unknown
            , IR.funcBody = IR.Int32 5
            }
        evalStateT
          (checkFunction (Map.fromList Size.builtins) mempty mempty mempty mempty input)
          (emptyTCState @Void) `shouldBe`
          Right output
      it "check `struct Pair<A, B>(A, B)`" $ do
        let
          result =
            flip evalStateT (emptyTCState) $
            checkADT
              mempty
              "Pair"
              ["A", "B"]
              (Syntax.Ctor
                "Pair"
                [Syntax.TVar . B $ Index Unknown 0, Syntax.TVar . B $ Index Unknown 1]
                Syntax.End
              )

        result `shouldBe`
          Right
            ( IR.Struct
              { IR.datatypeName = "Pair"
              , IR.datatypeTyArgs = [("A", KType), ("B", KType)]
              , IR.structFields = [(Nothing, TVar . B $ Index Unknown 0), (Nothing, TVar . B $ Index Unknown 1)]
              }
            , KArr KType $ KArr KType KType
            , CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CSized $ foldl @[] (TApp Unknown) (TName Unknown "Pair") [TVar . F $ B (), TVar $ B ()]
            , Size.Lam $ toScope $
              Size.Lam $ toScope $
              Size.Plus (Size.Var $ F $ B ()) (Size.Var $ B ())
            )
      it "check `struct Pair<F, A, B>(F<A>, F<B>)`" $ do
        let
          result =
            flip evalStateT emptyTCState $
            checkADT
              mempty
              "Pair"
              ["F", "A", "B"]
              (Syntax.Ctor
                 "Pair"
                 [ Syntax.TApp Unknown (Syntax.TVar . B $ Index Unknown 0) (Syntax.TVar . B $ Index Unknown 1)
                 , Syntax.TApp Unknown (Syntax.TVar . B $ Index Unknown 0) (Syntax.TVar . B $ Index Unknown 2)
                 ]
                 Syntax.End
              )
          fConstraint =
            CForall Nothing KType . CImplies (CSized . TVar $ B ()) $ -- a
            CSized $ foldl @[] (TApp Unknown) (TVar . F $ B ()) [TVar $ B ()]

        case result of
          Left err -> expectationFailure $ "Expected success, got failure: " <> show err
          Right (ctors, kind, constraint, size) -> do
            ctors `shouldBe`
              IR.Struct
              { IR.datatypeName = "Pair"
              , IR.datatypeTyArgs =
                  [ ("F", KArr KType KType)
                  , ("A", KType)
                  , ("B", KType)
                  ]
              , IR.structFields =
                  [ (Nothing, TApp Unknown (TVar . B $ Index Unknown 0) (TVar . B $ Index Unknown 1))
                  , (Nothing, TApp Unknown (TVar . B $ Index Unknown 0) (TVar . B $ Index Unknown 2))
                  ]
              }
            kind `shouldBe` KArr (KArr KType KType) (KArr KType $ KArr KType KType)
            constraint `shouldBe`
              CForall Nothing (KArr KType KType) (CImplies fConstraint $ -- f
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $ -- a
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $ -- b
              CSized $
              foldl @[]
                (TApp Unknown)
                (TName Unknown "Pair")
                [TVar . F . F $ B (), TVar . F $ B (), TVar $ B ()])
            size `shouldBe`
              Size.Lam (toScope $
              Size.Lam $ toScope $
              Size.Lam $ toScope $
              Size.Plus
                (Size.Var (F $ F $ B ()) .@ Size.Var (F $ B ()))
                (Size.Var (F $ F $ B ()) .@ Size.Var (B ())))
      it "check `struct Sum<A, B>{ Left(A), Right(B) }`" $ do
        let
          result =
            flip evalStateT emptyTCState $
            checkADT
              mempty
              "Sum"
              ["A", "B"]
              (Syntax.Ctor "Left" [Syntax.TVar . B $ Index Unknown 0] $
               Syntax.Ctor "Right" [Syntax.TVar . B $ Index Unknown 1] $
               Syntax.End)

        result `shouldBe`
          Right
            ( IR.Enum
              { IR.datatypeName = "Sum"
              , IR.datatypeTyArgs = [("A", KType), ("B", KType)]
              , IR.enumCtors =
                [ ("Left", [ (Nothing, TVar . B $ Index Unknown 0) ])
                , ("Right", [ (Nothing, TVar . B $ Index Unknown 1) ])
                ]
              }
            , KArr KType $ KArr KType KType
            -- forall t0. Sized t0 => forall t1. Sized t1 => Sized (Sum t0 t1)
            , CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CSized $ foldl @[] (TApp Unknown) (TName Unknown "Sum") [TVar . F $ B (), TVar $ B ()]
            , Size.Lam $ toScope $
              Size.Lam $ toScope $
              Size.Plus (Size.Word 1) $
              Size.Max (Size.Var $ F $ B ()) (Size.Var $ B ())
            )
      it "check `struct Box<A>(Ptr<A>)`" $ do
        let
          result =
            flip evalStateT (emptyTCState & globalTheory .~ Map.fromList Size.builtins) $
            checkADT
              mempty
              "Box"
              ["A"]
              (Syntax.Ctor "Box" [Syntax.TApp Unknown (Syntax.TPtr Unknown) . Syntax.TVar . B $ Index Unknown 0] $
               Syntax.End)

        result `shouldBe`
          Right
            ( IR.Struct
              { IR.datatypeName = "Box"
              , IR.datatypeTyArgs = [("A", KType)]
              , IR.structFields =
                  [ (Nothing, TApp Unknown (TPtr Unknown) (TVar . B $ Index Unknown 0))
                  ]
                }
            , KArr KType KType
            -- forall t0. Sized (Box t0)
            , CForall Nothing KType .
              CSized $ foldl @[] (TApp Unknown) (TName Unknown "Box") [TVar $ B ()]
            , Size.Word 8
            )
    describe "compile" $ do
      it "1" $ do
        let
          input =
            [ Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody = Syntax.Number Unknown 0
              }
            ]
          output =
            C.preamble <>
            [ C.Function C.Int32 "main" []
              [ C.Return $ C.Number 0
              ]
            ]
        case Compile.compile input of
          Left err -> expectationFailure $ "Expected success, got " <> show err
          Right code ->
            code `shouldBe` output
      it "2" $ do
        let
          input =
            [ Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "id"
              , Syntax.funcTyArgs = ["A"]
              , Syntax.funcArgs = [("x", TVar . B $ Index Unknown 0)]
              , Syntax.funcRetTy = TVar . B $ Index Unknown 0
              , Syntax.funcBody = Syntax.Var . B $ Index Unknown 0
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  Syntax.Call Unknown (Syntax.Name Unknown "id") [Syntax.Number Unknown 0]
              }
            ]
          output =
            C.preamble <>
            [ C.Function C.Int32 "id_TInt32" [(C.Int32, "x")]
              [ C.Return $ C.Var "x"
              ]
            , C.Function C.Int32 "main" []
              [ C.Return $ C.Call (C.Var "id_TInt32") [C.Number 0]
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code ->
            code `shouldBe` output
      it "3" $ do
        let
          input =
            [ Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  Syntax.Let
                    Unknown
                    [("x", Syntax.New Unknown $ Syntax.Number Unknown 26)]
                    (Syntax.Deref Unknown $ Syntax.Name Unknown "x")
              }
            ]
          output =
            C.preamble <>
            [ C.Function C.Int32 "main" []
              [ C.Declare (C.Ptr C.Int32) "__0" . Just $
                C.Cast (C.Ptr C.Int32) (C.Malloc $ C.Number 4)
              , C.Assign (C.Deref $ C.Var "__0") (C.Number 26)
              , C.Declare (C.Ptr C.Int32) "x" (Just $ C.Var "__0")
              , C.Return . C.Deref $ C.Var "x"
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code -> do
            code `shouldBe` output
      it "4" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "Pair"
              , Syntax.adtArgs = ["A", "B"]
              , Syntax.adtCtors =
                Syntax.Ctor "Pair" [TVar . B $ Index Unknown 0, TVar . B $ Index Unknown 1] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  Syntax.Let
                    Unknown
                    [ ( "x"
                      , Syntax.Call Unknown
                          (Syntax.Name Unknown "Pair")
                          [Syntax.BTrue Unknown, Syntax.BFalse Unknown]
                      )
                    ]
                    (Syntax.Number Unknown 99)
              }
            ]
          pairBoolBoolAnn = Just $ C.Ann "Pair bool bool"
          output =
            C.preamble <>
            [ C.Typedef (C.Name $ "struct Pair_TBool_TBool_t") "Pair_TBool_TBool_t"
            , C.Struct "Pair_TBool_TBool_t" [(C.Bool, "_0"), (C.Bool, "_1")]
            , C.Function
                (C.Name "Pair_TBool_TBool_t")
                "make_Pair_TBool_TBool"
                [ (C.Bool, "__0")
                , (C.Bool, "__1")
                ]
                [ C.Declare
                    (C.Name "Pair_TBool_TBool_t")
                    "__2"
                    (Just $ C.Init [(C.Var "__0"), (C.Var "__1")])
                , C.Return $ C.Var "__2"
                ]
            , C.Function C.Int32 "main" []
              [ C.Declare (C.Name "Pair_TBool_TBool_t") "x" . Just $
                C.Call
                  (C.Var "make_Pair_TBool_TBool")
                  [C.BTrue, C.BFalse]
              , C.Return $ C.Number 99
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code -> do
            code `shouldBe` output
      it "5" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "Pair"
              , Syntax.adtArgs = ["A", "B"]
              , Syntax.adtCtors =
                Syntax.Ctor "Pair" [TVar . B $ Index Unknown 0, TVar . B $ Index Unknown 1] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  Syntax.Let
                    Unknown
                    [ ( "x"
                      , Syntax.Call Unknown
                          (Syntax.Name Unknown "Pair")
                          [Syntax.Number Unknown 22, Syntax.Number Unknown 33]
                      )
                    ]
                    (Syntax.Project Unknown (Syntax.Name Unknown "x") "0")
              }
            ]
          output =
            C.preamble <>
            [ C.Typedef (C.Name $ "struct Pair_TInt32_TInt32_t") "Pair_TInt32_TInt32_t"
            , C.Struct "Pair_TInt32_TInt32_t" [(C.Int32, "_0"), (C.Int32, "_1")]
            , C.Function
                (C.Name "Pair_TInt32_TInt32_t")
                "make_Pair_TInt32_TInt32"
                [ (C.Int32, "__0")
                , (C.Int32, "__1")
                ]
                [ C.Declare
                    (C.Name "Pair_TInt32_TInt32_t")
                    "__2"
                    (Just $ C.Init [(C.Var "__0"), (C.Var "__1")])
                , C.Return $ C.Var "__2"
                ]
            , C.Function C.Int32 "main" []
              [ C.Declare (C.Name "Pair_TInt32_TInt32_t") "x" . Just $
                C.Call
                  (C.Var "make_Pair_TInt32_TInt32")
                  [C.Number 22, C.Number 33]
              , C.Return $ C.Project (C.Var "x") "_0"
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code -> do
            code `shouldBe` output
      it "6" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "List"
              , Syntax.adtArgs = ["A"]
              , Syntax.adtCtors =
                Syntax.Ctor "Nil" [] $
                Syntax.Ctor "Cons"
                  [ TVar . B $ Index Unknown 0
                  , TApp Unknown (TPtr Unknown) $ TApp Unknown (TName Unknown "List") (TVar . B $ Index Unknown 0)
                  ] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  Syntax.Let
                    Unknown
                    [("x", Syntax.Call Unknown (Syntax.Name Unknown "Nil") [])]
                    (Syntax.Number Unknown 0)
              }
            ]
          output =
            C.preamble <>
            [ C.Typedef (C.Name "struct List_TInt32_t") "List_TInt32_t"
            , C.Struct "List_TInt32_t"
              [ (C.UInt8, "tag")
              , ( C.Union
                  [ (C.TStruct [],"Nil")
                  , (C.TStruct [(C.Int32,"_0"), (C.Ptr (C.Name "List_TInt32_t"),"_1")],"Cons")
                  ]
                , "data"
                )
              ]
            , C.Function (C.Name "List_TInt32_t") "make_Nil_TInt32" []
              [ C.Declare (C.Name "List_TInt32_t") "__0" . Just $
                C.Init [C.Number 0, C.InitNamed [("Nil", C.Init [])]]
              , C.Return (C.Var "__0")
              ]
            , C.Function C.Int32 "main" []
              [ C.Declare (C.Name "List_TInt32_t") "x" . Just $
                C.Call (C.Var "make_Nil_TInt32") []
              , C.Return $ C.Number 0
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code -> do
            code `shouldBe` output
      it "7" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "List"
              , Syntax.adtArgs = ["A"]
              , Syntax.adtCtors =
                Syntax.Ctor "Nil" [] $
                Syntax.Ctor "Cons"
                  [ TVar . B $ Index Unknown 0
                  , TApp Unknown (TPtr Unknown) $ TApp Unknown (TName Unknown "List") (TVar . B $ Index Unknown 0)
                  ] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  let
                    e =
                      Syntax.Call Unknown
                        (Syntax.Name Unknown "Cons")
                        [ Syntax.Number Unknown 1
                        , Syntax.New Unknown $ Syntax.Call Unknown (Syntax.Name Unknown "Nil") []
                        ]
                  in
                    Syntax.Match Unknown e
                      [ Syntax.Case Unknown "Nil" [] $ Syntax.Number Unknown 0
                      , Syntax.Case Unknown "Cons" ["a", "b"] $
                        Syntax.Var (B $ Index Unknown 0)
                      ]
              }
            ]
          output =
            C.preamble <>
            [ C.Typedef (C.Name "struct List_TInt32_t") "List_TInt32_t"
            , C.Struct "List_TInt32_t"
              [ (C.UInt8, "tag")
              , ( C.Union
                  [ (C.TStruct [],"Nil")
                  , (C.TStruct [(C.Int32,"_0"), (C.Ptr (C.Name "List_TInt32_t"),"_1")],"Cons")
                  ]
                , "data"
                )
              ]
            , C.Function
                (C.Name "List_TInt32_t")
                "make_Cons_TInt32"
                [(C.Int32, "__0"), (C.Ptr $ C.Name "List_TInt32_t", "__1")]
                [ C.Declare (C.Name "List_TInt32_t") "__2" . Just $
                  C.Init [C.Number 1, C.InitNamed [("Cons", C.Init [C.Var "__0", C.Var "__1"])]]
                , C.Return (C.Var "__2")
                ]
            , C.Function (C.Name "List_TInt32_t") "make_Nil_TInt32" []
              [ C.Declare (C.Name "List_TInt32_t") "__3" . Just $
                C.Init [C.Number 0, C.InitNamed [("Nil", C.Init [])]]
              , C.Return (C.Var "__3")
              ]
            , C.Function C.Int32 "main" []
              [ C.Declare (C.Ptr $ C.Name "List_TInt32_t") "__4" . Just $
                C.Cast (C.Ptr $ C.Name "List_TInt32_t") (C.Malloc $ C.Number 13)
              , C.Assign (C.Deref (C.Var "__4")) $ C.Call (C.Var "make_Nil_TInt32") []

              , C.Declare (C.Name "List_TInt32_t") "__5" . Just $
                C.Call (C.Var "make_Cons_TInt32") [C.Number 1, C.Var "__4"]

              , C.Declare C.Int32 "__6" Nothing

              , C.If (C.Eq (C.Project (C.Var "__5") "tag") (C.Number 0))
                [ C.Assign (C.Var "__6") (C.Number 0)
                ]

              , C.If (C.Eq (C.Project (C.Var "__5") "tag") (C.Number 1))
                [ C.Assign (C.Var "__6") (C.Project (C.Project (C.Project (C.Var "__5") "data") "Cons") "_0")
                ]

              , C.Return $ C.Var "__6"
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code -> do
            code `shouldBe` output
      it "8" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "List"
              , Syntax.adtArgs = ["A"]
              , Syntax.adtCtors =
                Syntax.Ctor "Nil" [] $
                Syntax.Ctor "Cons"
                  [ TVar . B $ Index Unknown 0
                  , TApp Unknown (TPtr Unknown) $ TApp Unknown (TName Unknown "List") (TVar . B $ Index Unknown 0)
                  ] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  let
                    e =
                      Syntax.Call Unknown
                        (Syntax.Name Unknown "Cons")
                        [ Syntax.BTrue Unknown
                        , Syntax.New Unknown $ Syntax.Call Unknown (Syntax.Name Unknown "Nil") []
                        ]
                  in
                    Syntax.Match Unknown e
                      [ Syntax.Case Unknown "Nil" [] $ Syntax.Number Unknown 0
                      , Syntax.Case Unknown "Cons" ["a", "b"] $
                        Syntax.Var (B $ Index Unknown 0)
                      ]
              }
            ]
        case Compile.compile input of
          Left err ->
            err `shouldBe`
            Compile.TypeError (TypeMismatch Unknown (TypeM $ TInt32 Unknown) (TypeM $ TBool Unknown))
          Right code -> expectationFailure $ "expected error, got " <> show code
      it "9" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "Either"
              , Syntax.adtArgs = ["A", "B"]
              , Syntax.adtCtors =
                Syntax.Ctor "Left" [TVar . B $ Index Unknown 0] $
                Syntax.Ctor "Right" [TVar . B $ Index Unknown 1] $
                Syntax.End
              }
            , Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "List"
              , Syntax.adtArgs = ["A"]
              , Syntax.adtCtors =
                Syntax.Ctor "Nil" [] $
                Syntax.Ctor "Cons"
                  [ TVar . B $ Index Unknown 0
                  , TApp Unknown (TPtr Unknown) $ TApp Unknown (TName Unknown "List") (TVar . B $ Index Unknown 0)
                  ] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  let
                    e =
                      -- Cons(1, new[Nil()])
                      Syntax.Call Unknown
                        (Syntax.Name Unknown "Cons")
                        [ Syntax.Number Unknown 1
                        , Syntax.New Unknown $ Syntax.Call Unknown (Syntax.Name Unknown "Nil") []
                        ]
                  in
                    -- match Cons(1, new[Nil()]) {
                    --   Left(a) => a
                    --   Cons(a, b) => a
                    -- }
                    Syntax.Match Unknown e
                      [ Syntax.Case Unknown "Left" ["a"] $
                        Syntax.Var (B $ Index Unknown 0)
                      , Syntax.Case Unknown "Cons" ["a", "b"] $
                        Syntax.Var (B $ Index Unknown 0)
                      ]
              }
            ]
        case Compile.compile input of
          Left err ->
            err `shouldBe`
            Compile.TypeError
              (TypeMismatch
                Unknown
                (TypeM $
                 TApp Unknown (TName Unknown "List") (TInt32 Unknown)
                )
                (TypeM $
                 foldl @[] (TApp Unknown)
                   (TName Unknown "Either")
                   [ TVar . Left $ TMeta Unknown 7
                   , TVar . Left $ TMeta Unknown 8
                   ]
                )
              )
          Right code -> expectationFailure $ "expected error, got " <> show code
      it "10" $ do
        let
          input =
            [ Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "Identity"
              , Syntax.adtArgs = ["A"]
              , Syntax.adtCtors =
                Syntax.Ctor "Identity" [TVar . B $ Index Unknown 0] $
                Syntax.End
              }
            , Syntax.DData $
              Syntax.ADT
              { Syntax.adtName = "List"
              , Syntax.adtArgs = ["F", "A"]
              , Syntax.adtCtors =
                Syntax.Ctor "Nil" [] $
                Syntax.Ctor "Cons"
                  [ TApp Unknown (TVar . B $ Index Unknown 0) (TVar . B $ Index Unknown 1)
                  , TApp Unknown (TPtr Unknown) $
                    foldl @[] (TApp Unknown)
                      (TName Unknown "List")
                      [TVar . B $ Index Unknown 0, TVar . B $ Index Unknown 1]
                  ]
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt32 Unknown
              , Syntax.funcBody =
                  let
                    e =
                      Syntax.Call Unknown
                        (Syntax.Name Unknown "Cons")
                        [ Syntax.Call Unknown (Syntax.Name Unknown "Identity") [Syntax.Number Unknown 1]
                        , Syntax.New Unknown $ Syntax.Call Unknown (Syntax.Name Unknown "Nil") []
                        ]
                  in
                    Syntax.Match Unknown e
                      [ Syntax.Case Unknown "Nil" [] $ Syntax.Number Unknown 0
                      , Syntax.Case Unknown "Cons" ["a", "b"] $
                        Syntax.Project Unknown (Syntax.Var (B $ Index Unknown 0)) "0"
                      ]
              }
            ]
        case Compile.compile input of
          Left err -> expectationFailure $ "expected success, got " <> show err
          Right code -> do
            let
              output =
                C.preamble <>
                [ C.Typedef (C.Name "struct Identity_TInt32_t") "Identity_TInt32_t"
                , C.Struct "Identity_TInt32_t" [(C.Int32,"_0")]

                , C.Typedef (C.Name "struct List_Identity_TInt32_t") "List_Identity_TInt32_t"
                , C.Struct "List_Identity_TInt32_t"
                  [ (C.UInt8, "tag")
                  , ( C.Union
                      [ (C.TStruct [],"Nil")
                      , ( C.TStruct
                          [ (C.Name "Identity_TInt32_t","_0")
                          , (C.Ptr (C.Name "List_Identity_TInt32_t"),"_1")
                          ]
                        ,"Cons"
                        )
                      ]
                    , "data"
                    )
                  ]

                , C.Function
                    (C.Name "List_Identity_TInt32_t")
                    "make_Cons_Identity_TInt32"
                    [(C.Name "Identity_TInt32_t", "__0"), (C.Ptr $ C.Name "List_Identity_TInt32_t", "__1")]
                    [ C.Declare (C.Name "List_Identity_TInt32_t") "__2" . Just $
                      C.Init [C.Number 1, C.InitNamed [("Cons", C.Init [C.Var "__0", C.Var "__1"])]]
                    , C.Return (C.Var "__2")
                    ]

                , C.Function (C.Name "Identity_TInt32_t") "make_Identity_TInt32" [(C.Int32, "__3")]
                  [ C.Declare (C.Name "Identity_TInt32_t") "__4" . Just $ C.Init [C.Var "__3"]
                  , C.Return (C.Var "__4")
                  ]

                , C.Function (C.Name "List_Identity_TInt32_t") "make_Nil_Identity_TInt32" []
                  [ C.Declare (C.Name "List_Identity_TInt32_t") "__5" . Just $
                    C.Init [C.Number 0, C.InitNamed [("Nil", C.Init [])]]
                  , C.Return (C.Var "__5")
                  ]

                , C.Function C.Int32 "main" []
                  [ C.Declare (C.Ptr $ C.Name "List_Identity_TInt32_t") "__6" . Just $
                    C.Cast (C.Ptr $ C.Name "List_Identity_TInt32_t") (C.Malloc $ C.Number 13)
                  , C.Assign (C.Deref (C.Var "__6")) $ C.Call (C.Var "make_Nil_Identity_TInt32") []

                  , C.Declare (C.Name "List_Identity_TInt32_t") "__7" . Just $
                    C.Call (C.Var "make_Cons_Identity_TInt32")
                      [C.Call (C.Var "make_Identity_TInt32") [C.Number 1], C.Var "__6"]

                  , C.Declare C.Int32 "__8" Nothing

                  , C.If (C.Eq (C.Project (C.Var "__7") "tag") (C.Number 0))
                    [ C.Assign (C.Var "__8") (C.Number 0)
                    ]

                  , C.If (C.Eq (C.Project (C.Var "__7") "tag") (C.Number 1))
                    [ C.Assign (C.Var "__8") $
                      C.Project (C.Project (C.Project (C.Project (C.Var "__7") "data") "Cons") "_0") "_0"
                    ]

                  , C.Return $ C.Var "__8"
                  ]
                ]
            code `shouldBe` output
