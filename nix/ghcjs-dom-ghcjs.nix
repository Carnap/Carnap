{ mkDerivation, base, ghc-prim, ghcjs-base, ghcjs-prim, stdenv
, text, transformers
}:
mkDerivation {
  pname = "ghcjs-dom";
  version = "0.2.4.0";
  sha256 = "986db6b770c348d7a28368309a648626455d55e7a5705a849fd5a2981eb868a6";
  libraryHaskellDepends = [
    base ghc-prim ghcjs-base ghcjs-prim text transformers
  ];
  description = "DOM library that supports both GHCJS and WebKitGTK";
  license = stdenv.lib.licenses.mit;
}
