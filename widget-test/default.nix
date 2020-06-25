{ system ? builtins.currentSystem }:
let
  nixpkgs = (import ../reflex-platform { inherit system; }).nixpkgs;
  widget = (import ../. { inherit system; }).ghcjs.widget;
in
  nixpkgs.stdenv.mkDerivation {
    name = "widget-test";
    src = ./.;
    buildInputs = [ widget ];
    buildPhase = ''
      echo "nothing to do"
    '';
    installPhase = ''
      mkdir -p $out/lib
      cp -R ${widget}/bin/widget.jsexe/* $out/lib/
      cp index.html $out
    '';
  }