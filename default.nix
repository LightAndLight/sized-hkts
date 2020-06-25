{ system ? builtins.currentSystem }:
(import ./reflex-platform { inherit system; useTextJSString = false; }).project ({ pkgs, ... }: {
  overrides = self: super: {
    diagnostica = self.callCabal2nix "diagnostica" (
      pkgs.fetchFromGitHub {
        owner = "LightAndLight";
        repo = "diagnostica";
        rev = "3401509dab8c42d1458d20a48d747fd8ca66bf3a";
        sha256 = "0pvhvnvkl34m5mg8rxrhlb3sfqs9mdjqjqhk6cpxn6hbixz7adlf";
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
        rev = "8236d4dd39ddf58371e8cb70509a9d1324b110eb";
        sha256 = "0bxxhl8hj6c6yzqazsza7nw2pck22z180b5bjsg9hi1k24h6g1xv";
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