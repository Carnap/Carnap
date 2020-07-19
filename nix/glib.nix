{ mkDerivation, base, bytestring, Cabal, containers, glib
, gtk2hs-buildtools, stdenv, text, utf8-string
}:
mkDerivation {
  pname = "glib";
  version = "0.13.8.1";
  sha256 = "dcd028ac6d4a7476c14585be1d845b8c4aea4c389f34e809ed1a8df7425c1a9c";
  setupHaskellDepends = [ base Cabal gtk2hs-buildtools ];
  libraryHaskellDepends = [
    base bytestring containers text utf8-string
  ];
  libraryPkgconfigDepends = [ glib ];
  homepage = "http://projects.haskell.org/gtk2hs/";
  description = "Binding to the GLIB library for Gtk2Hs";
  license = stdenv.lib.licenses.lgpl21;
}
