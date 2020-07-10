{ mkDerivation, aeson, base, bytestring, exceptions, http-conduit
, http-types, microlens, stdenv, text, unordered-containers
, uri-bytestring, uri-bytestring-aeson
}:
mkDerivation {
  pname = "hoauth2";
  version = "1.8.4";
  sha256 = "5d5313221980bad30a30649633c821ad25604b09dd9065aa2170115cda5ff14c";
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base bytestring exceptions http-conduit http-types microlens
    text unordered-containers uri-bytestring uri-bytestring-aeson
  ];
  homepage = "https://github.com/freizl/hoauth2";
  description = "Haskell OAuth2 authentication client";
  license = stdenv.lib.licenses.bsd3;
}
