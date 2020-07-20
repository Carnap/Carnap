{ mkDerivation, aeson, base, blaze-html, bytestring, Carnap
, Carnap-Client, containers, ghcjs-dom, hashable, lens, mtl, parsec
, shakespeare, stdenv, tagsoup, text, transformers
}:
mkDerivation {
  pname = "Carnap-GHCJS";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base blaze-html bytestring Carnap Carnap-Client containers
    ghcjs-dom hashable lens mtl parsec shakespeare tagsoup text
    transformers
  ];
  executableHaskellDepends = [ base ];
  description = "GHCJS-compiled Components for Carnap Proof Assistant";
  license = stdenv.lib.licenses.gpl3;
}
