{ mkDerivation, base, blaze-html, blaze-markup, bytestring
, directory, hspec, pandoc, persistent, shakespeare, stdenv, text
, xss-sanitize, yesod-core, yesod-form
}:
mkDerivation {
  pname = "yesod-markdown";
  version = "0.12.4";
  sha256 = "04992ec30cdfc6f44f37c787a32e6d039f86992dea1399157538d9557a93d791";
  libraryHaskellDepends = [
    base blaze-html blaze-markup bytestring directory pandoc persistent
    shakespeare text xss-sanitize yesod-core yesod-form
  ];
  testHaskellDepends = [ base blaze-html hspec text ];
  homepage = "http://github.com/pbrisbin/yesod-markdown";
  description = "Tools for using markdown in a yesod application";
  license = stdenv.lib.licenses.gpl2;
}
