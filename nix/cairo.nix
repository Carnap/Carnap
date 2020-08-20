{ mkDerivation, array, base, bytestring, Cabal, cairo
, gtk2hs-buildtools, mtl, stdenv, text, utf8-string
}:
mkDerivation {
  pname = "cairo";
  version = "0.13.8.1";
  sha256 = "1316412d51556205cfc097a354eddf0e51f4d319cde0498626a2854733f4f3c2";
  enableSeparateDataOutput = true;
  setupHaskellDepends = [ base Cabal gtk2hs-buildtools ];
  libraryHaskellDepends = [
    array base bytestring mtl text utf8-string
  ];
  libraryPkgconfigDepends = [ cairo ];
  homepage = "http://projects.haskell.org/gtk2hs/";
  description = "Binding to the Cairo library";
  license = stdenv.lib.licenses.bsd3;
}
