{ system ? builtins.currentSystem }:
(import ./reflex-platform { inherit system; }).project ({ pkgs, ... }: {
  overrides = self: super: {
    diagnostica = self.callCabal2nix "diagnostica" (
      pkgs.fetchFromGitHub {
        owner = "LightAndLight";
        repo = "diagnostica";
        rev = "af0cd4cde27d0b491631cd028bebe7da8c87fe5e";
        sha256 = "19cc9fmn6970dsrj8xan3grzl0pqmh7c59rschli37b4dchz1kcf";
      }
    ) {};
    diagnostica-sage = self.callCabal2nix "diagnostica-sage" (
      pkgs.fetchFromGitHub {
        owner = "LightAndLight";
        repo = "diagnostica-sage";
        rev = "d4efe5cbeffaf6797d2558113ffcd989dc24a68c";
        sha256 = "1x709jhq4pvkr2zngn4h7jdji5w3j3ak64pav3cp9pzy7bd6ajiq";
      }
    ) {};
    sage = self.callCabal2nix "sage" (
      pkgs.fetchFromGitHub {
        owner = "LightAndLight";
        repo = "sage";
        rev = "f6d8ac89be98e046c782172904a0989a90a17bd4";
        sha256 = "0x8198bm75ay9mwh3l3yyq2wpxjxjdchyi2ij0gf4h2m40507m80";
      }
    ) {};
  };

  packages = {
    widget = ./widget;
    sized-hkts = ./.;
  };

  shells = {
    ghc = ["widget"];
    ghcjs = ["widget"];
  };
})