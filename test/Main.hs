{-# language OverloadedLists, OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language TypeApplications #-}
module Main where

import Bound.Scope (toScope)
import Bound.Var (Var(..))
import Control.Lens.Setter ((.~))
import Control.Monad.Except (runExceptT)
import Control.Monad.State (evalState, evalStateT)
import Control.Monad.Trans.Maybe (runMaybeT)
import Data.Function ((&))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Void (Void, absurd)
import Test.Hspec

import Check.Datatype (checkADT)
import Check.Entailment
  ( SMeta(..), Theory(..)
  , composeSSubs
  , emptyEntailState, globalTheory
  , freshSMeta, simplify, solve
  )
import Check.Function (checkFunction)
import Check.TypeError (TypeError(..))
import qualified Codegen.C as C
import qualified Compile
import Size ((.@), Size)
import qualified Size (Size(..), pattern Var)
import qualified Size.Builtins as Size (builtins)
import IR (Constraint(..), Kind(..))
import qualified IR
import Syntax (Type(..), WordSize(..))
import qualified Syntax
import TCState (TMeta, emptyTCState)
import Typecheck (sizeConstraintFor)

main :: IO ()
main =
  hspec $ do
    describe "sizeConstraintFor" $ do
      it "*" $
        sizeConstraintFor @Void KType `shouldBe` CSized (TVar $ B ())
      it "* -> *" $
        sizeConstraintFor @Void (KArr KType KType) `shouldBe`
        CForall Nothing KType
          (CImplies
             (CSized (TVar $ B ()))
             (CSized $
              TApp
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
              TApp
                (TApp
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
                (CSized $ TApp (TVar $ F $ B ()) (TVar $ B ()))
             ) $
           -- Sized (#0 x y)
           CSized $
           TApp
             (TApp
               (TVar $ F $ F $ B ())
               (TVar $ F $ B ())
             )
             (TVar $ B ())
          )
    describe "entailment" $ do
      it "simplify { (8, Sized U64) } (d0 : Sized U64) ==> [d0 := 8]" $ do
        let
          theory :: Theory (Either TMeta Void)
          theory =
            Theory
            { _thGlobal =
              [ (CSized $ TUInt S64, Size.Word 8)
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyEntailState emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (,) m <$> simplify mempty absurd absurd theory (m, CSized $ TUInt S64)
        case e_res of
          Left{} -> expectationFailure "expected success, got error"
          Right (d0, res) -> res `shouldBe` ([], [(d0, Size.Word 8 :: Size (Either SMeta Void))])
      it "solve $ simplify { (8, Sized U64), (\\x -> x + x, forall a. Sized a => Sized (Pair a)) } (d0 : Sized (Pair U64)) ==> [d0 := 16]" $ do
        let
          kindScope =
            [ ("Pair", KArr KType $ KArr KType KType)
            ]

          theory :: Theory (Either TMeta Void)
          theory =
            Theory
            { _thGlobal =
              [ (CSized $ TUInt S64, Size.Word 8)
              , ( CForall (Just "a") KType $
                  CImplies
                    (CSized $ TVar $ B ())
                    (CSized $ TApp (TName "Pair") (TVar $ B ()))
                , Size.Lam . toScope $ Size.Plus (Size.Var $ B ()) (Size.Var $ B ())
                )
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyEntailState emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (assumes, sols) <-
              fmap (fromMaybe ([], mempty)) . runMaybeT $
              simplify kindScope absurd absurd theory (m, CSized $ TApp (TName "Pair") (TUInt S64))
            (assumes', sols') <- solve kindScope absurd absurd theory assumes
            pure (m, (assumes', composeSSubs sols' sols))
        case e_res of
          Left err -> expectationFailure $ "expected success, got error: " <> show err
          Right (d0, (assumes, sols)) ->
            Map.lookup d0 sols `shouldBe` Just (Size.Word 16 :: Size (Either SMeta Void))
      it "solve $ simplify { (\\x -> x + x, forall a. Sized a => Sized (Pair a)) } (d0 : Sized (Pair U64)) ==> cannot deduce  Sized U64" $ do
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
                    (CSized $ TApp (TName "Pair") (TVar $ B ()))
                , Size.Lam . toScope $ Size.Plus (Size.Var $ B ()) (Size.Var $ B ())
                )
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyEntailState emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (assumes, sols) <-
              fmap (fromMaybe ([], mempty)) . runMaybeT $
              simplify kindScope absurd absurd theory (m, CSized $ TApp (TName "Pair") (TUInt S64))
            (assumes', sols') <- solve kindScope absurd absurd theory assumes
            pure (m, (assumes', composeSSubs sols' sols))
        case e_res of
          Left err -> err `shouldBe` CouldNotDeduce (CSized $ TUInt S64)
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
                    (CSized $ TApp (TName "Pair") (TVar $ B ()))
                , Size.Lam . toScope $ Size.Plus (Size.Var $ B ()) (Size.Var $ B ())
                )
              ]
            , _thLocal = mempty
            }
          e_res = flip evalState (emptyEntailState emptyTCState) . runExceptT $ do
            m <- freshSMeta
            (assumes, sols) <-
              fmap (fromMaybe ([], mempty)) . runMaybeT $
              simplify mempty absurd absurd theory
                ( m
                , CForall (Just "a") KType $
                  CImplies
                    (CSized $ TApp (TName "Pair") (TVar $ B ()))
                    (CSized $ TVar $ B ())
                )
            (assumes', sols') <- solve @_ @Void mempty absurd absurd theory assumes
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
            , Syntax.funcArgs = [("x", TVar $ B 0)]
            , Syntax.funcRetTy = TVar $ B 0
            , Syntax.funcBody = Syntax.Var $ B 0
            }
          output =
            IR.Function
            { IR.funcName = "id"
            , IR.funcTyArgs = [("A", KType)]
            , IR.funcConstraints = [CSized $ TVar $ B 0]
            , IR.funcArgs = [("x", TVar $ B 0)]
            , IR.funcRetTy = TVar $ B 0
            , IR.funcBody = IR.Var $ B 0
            }
        evalStateT (checkFunction mempty mempty input) (emptyTCState @Void) `shouldBe`
          Right output
      it "five() -> int32" $ do
        let
          input =
            Syntax.Function
            { Syntax.funcName = "five"
            , Syntax.funcTyArgs = []
            , Syntax.funcArgs = []
            , Syntax.funcRetTy = TInt S32
            , Syntax.funcBody = Syntax.Number 5
            }
          output =
            IR.Function
            { IR.funcName = "five"
            , IR.funcTyArgs = []
            , IR.funcConstraints = []
            , IR.funcArgs = []
            , IR.funcRetTy = TInt S32
            , IR.funcBody = IR.Int32 5
            }
        evalStateT
          (checkFunction mempty mempty input)
          (emptyTCState @Void & globalTheory .~ Map.fromList Size.builtins) `shouldBe`
          Right output
      it "check `struct Pair<A, B>(A, B)`" $ do
        let
          result =
            flip evalStateT (emptyEntailState emptyTCState) $
            checkADT
              mempty
              "Pair"
              ["A", "B"]
              (Syntax.Ctor
                "Pair"
                [Syntax.TVar $ B 0, Syntax.TVar $ B 1]
                Syntax.End
              )

        result `shouldBe`
          Right
            ( [ IR.Constructor
                { IR.ctorName = "Pair"
                , IR.ctorTyArgs = [("A", KType), ("B", KType)]
                , IR.ctorArgs = [(Nothing, TVar $ B 0), (Nothing, TVar $ B 1)]
                , IR.ctorRetTy =
                    foldl @[] TApp (TName "Pair") [TVar $ B 0, TVar $ B 1]
                }
              ]
            , KArr KType $ KArr KType KType
            , CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CSized $ foldl @[] TApp (TName "Pair") [TVar . F $ B (), TVar $ B ()]
            , Size.Lam $ toScope $
              Size.Lam $ toScope $
              Size.Plus (Size.Var $ F $ B ()) (Size.Var $ B ())
            )
      it "check `struct Pair<F, A, B>(F<A>, F<B>)`" $ do
        let
          result =
            flip evalStateT (emptyEntailState emptyTCState) $
            checkADT
              mempty
              "Pair"
              ["F", "A", "B"]
              (Syntax.Ctor
                 "Pair"
                 [ Syntax.TApp (Syntax.TVar $ B 0) (Syntax.TVar $ B 1)
                 , Syntax.TApp (Syntax.TVar $ B 0) (Syntax.TVar $ B 2)
                 ]
                 Syntax.End
              )
          fConstraint =
            CForall Nothing KType . CImplies (CSized . TVar $ B ()) $ -- a
            CSized $ foldl @[] TApp (TVar . F $ B ()) [TVar $ B ()]

        case result of
          Left err -> expectationFailure $ "Expected success, got failure: " <> show err
          Right (ctors, kind, constraint, size) -> do
            ctors `shouldBe`
              [ IR.Constructor
                { IR.ctorName = "Pair"
                , IR.ctorTyArgs =
                    [ ("F", KArr KType KType)
                    , ("A", KType)
                    , ("B", KType)
                    ]
                , IR.ctorArgs =
                    [ (Nothing, TApp (TVar $ B 0) (TVar $ B 1))
                    , (Nothing, TApp (TVar $ B 0) (TVar $ B 2))
                    ]
                , IR.ctorRetTy =
                    foldl
                      @[]
                      TApp
                      (TName "Pair")
                      [TVar $ B 0, TVar $ B 1, TVar $ B 2]
                }
              ]
            kind `shouldBe` KArr (KArr KType KType) (KArr KType $ KArr KType KType)
            constraint `shouldBe`
              CForall Nothing (KArr KType KType) (CImplies fConstraint $ -- f
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $ -- a
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $ -- b
              CSized $ foldl @[] TApp (TName "Pair") [TVar . F . F $ B (), TVar . F $ B (), TVar $ B ()])
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
            flip evalStateT (emptyEntailState emptyTCState) $
            checkADT
              mempty
              "Sum"
              ["A", "B"]
              (Syntax.Ctor "Left" [Syntax.TVar $ B 0] $
               Syntax.Ctor "Right" [Syntax.TVar $ B 1] $
               Syntax.End)

        result `shouldBe`
          Right
            ( [ IR.Constructor
                { IR.ctorName = "Left"
                , IR.ctorTyArgs = [("A", KType), ("B", KType)]
                , IR.ctorArgs =
                    [ (Nothing, TVar $ B 0)
                    ]
                , IR.ctorRetTy =
                    foldl
                      @[]
                      TApp
                      (TName "Sum")
                      [TVar $ B 0, TVar $ B 1]
                }
              , IR.Constructor
                { IR.ctorName = "Right"
                , IR.ctorTyArgs = [("A", KType), ("B", KType)]
                , IR.ctorArgs =
                    [ (Nothing, TVar $ B 1)
                    ]
                , IR.ctorRetTy =
                    foldl
                      @[]
                      TApp
                      (TName "Sum")
                      [TVar $ B 0, TVar $ B 1]
                }
              ]
            , KArr KType $ KArr KType KType
            -- forall t0. Sized t0 => forall t1. Sized t1 => Sized (Sum t0 t1)
            , CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CForall Nothing KType . CImplies (CSized . TVar $ B ()) $
              CSized $ foldl @[] TApp (TName "Sum") [TVar . F $ B (), TVar $ B ()]
            , Size.Lam $ toScope $
              Size.Lam $ toScope $
              Size.Plus (Size.Word 1) $
              Size.Max (Size.Var $ F $ B ()) (Size.Var $ B ())
            )
      it "check `struct Box<A>(Ptr<A>)`" $ do
        let
          result =
            flip evalStateT (emptyEntailState emptyTCState & globalTheory .~ Map.fromList Size.builtins) $
            checkADT
              mempty
              "Box"
              ["A"]
              (Syntax.Ctor "Box" [Syntax.TApp Syntax.TPtr . Syntax.TVar $ B 0] $
               Syntax.End)

        result `shouldBe`
          Right
            ( [ IR.Constructor
                { IR.ctorName = "Box"
                , IR.ctorTyArgs = [("A", KType)]
                , IR.ctorArgs =
                    [ (Nothing, TApp TPtr (TVar $ B 0))
                    ]
                , IR.ctorRetTy =
                    TApp (TName "Box") (TVar $ B 0)
                }
              ]
            , KArr KType KType
            -- forall t0. Sized (Box t0)
            , CForall Nothing KType .
              CSized $ foldl @[] TApp (TName "Box") [TVar $ B ()]
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
              , Syntax.funcRetTy = TInt S32
              , Syntax.funcBody = Syntax.Number 0
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
              , Syntax.funcArgs = [("x", TVar $ B 0)]
              , Syntax.funcRetTy = TVar $ B 0
              , Syntax.funcBody = Syntax.Var $ B 0
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt S32
              , Syntax.funcBody =
                  Syntax.Call (Syntax.Name "id") [Syntax.Number 0]
              }
            ]
          output =
            C.preamble <>
            [ C.Function C.Int32 "id_TInt32" [(C.Int32, "x")]
              [ C.Return $ C.Var "x"
              ]
            , C.Function C.Int32 "main" []
              [ C.Return $ C.Call (C.Var "id") [C.Number 0]
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
              , Syntax.funcRetTy = TInt S32
              , Syntax.funcBody =
                  Syntax.Let
                    [("x", Syntax.New $ Syntax.Number 26)]
                    (Syntax.Deref $ Syntax.Name "x")
              }
            ]
          output =
            C.preamble <>
            [ C.Function C.Int32 "main" []
              [ C.Declare (C.Ptr C.Int32) "__0" $
                C.Cast (C.Ptr C.Int32) (C.Malloc $ C.Number 4)
              , C.Assign (C.Deref $ C.Var "__0") (C.Number 26)
              , C.Declare (C.Ptr C.Int32) "x" (C.Var "__0")
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
                Syntax.Ctor "Pair" [TVar $ B 0, TVar $ B 1] $
                Syntax.End
              }
            , Syntax.DFunc $
              Syntax.Function
              { Syntax.funcName = "main"
              , Syntax.funcTyArgs = []
              , Syntax.funcArgs = []
              , Syntax.funcRetTy = TInt S32
              , Syntax.funcBody =
                  Syntax.Let
                    [ ( "x"
                      , Syntax.Call
                          (Syntax.Name "Pair")
                          [Syntax.BTrue, Syntax.BFalse]
                      )
                    ]
                    (Syntax.Number 99)
              }
            ]
          pairBoolBoolAnn = Just $ C.Ann "Pair bool bool"
          output =
            C.preamble <>
            [ C.Function
                (C.Ptr $ C.Void pairBoolBoolAnn)
                "Pair_TBool_TBool"
                [ (C.Ptr $ C.Void pairBoolBoolAnn, "__0")
                , (C.Bool, "__1")
                , (C.Bool, "__2")
                ]
                [ C.Assign (C.Index (C.Var "__0") 0) (C.Var "__1")
                , C.Assign (C.Index (C.Var "__0") 1) (C.Var "__2")
                , C.Return $ C.Var "__0"
                ]
            , C.Function C.Int32 "main" []
              [ C.Declare (C.Ptr $ C.Void pairBoolBoolAnn) "__3" $
                C.Cast (C.Ptr $ C.Void Nothing) (C.Alloca $ C.Number 2)
              , C.Declare (C.Void Nothing) "__4" $
                C.Call
                  (C.Var "Pair_TBool_TBool")
                  [C.Var "__3", C.BTrue, C.BFalse]
              , C.Declare (C.Ptr $ C.Void Nothing) "x" (C.Var "__3")
              , C.Return $ C.Number 99
              ]
            ]
        case Compile.compile input of
          Left err ->
            expectationFailure $
            "Expected success, got " <> show err
          Right code -> do
            code `shouldBe` output
