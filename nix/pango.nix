{ mkDerivation, array, base, Cabal, cairo, containers, directory
, filepath, glib, gtk2hs-buildtools, mtl, pango, pretty, process
, stdenv, text
}:
mkDerivation {
  pname = "pango";
  version = "0.13.8.1";
  sha256 = "40a67a56687969cee9dd4cc94a8a3d0beb5ea687c8a2f3da552feb915453c82f";
  enableSeparateDataOutput = true;
  setupHaskellDepends = [ base Cabal filepath gtk2hs-buildtools ];
  libraryHaskellDepends = [
    array base cairo containers directory glib mtl pretty process text
  ];
  libraryPkgconfigDepends = [ pango ];
  homepage = "http://projects.haskell.org/gtk2hs/";
  description = "Binding to the Pango text rendering engine";
  license = stdenv.lib.licenses.lgpl21;
}
