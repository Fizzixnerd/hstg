{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    haskell.compiler.ghc921
    haskell-language-server
    cabal-install
    llvm_12
  ];
}
