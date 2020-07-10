{ mkDerivation, base, containers, hashable, lens, logict, mtl
, parsec, shakespeare, stdenv, text, transformers
}:
mkDerivation {
  pname = "Carnap";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base containers hashable lens logict mtl parsec transformers
  ];
  doCheck = false;
  testHaskellDepends = [ base shakespeare text ];
  description = "Libraries for the Carnap Proof Assistant";
  license = stdenv.lib.licenses.gpl3;
}
