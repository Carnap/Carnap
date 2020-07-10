{ mkDerivation, aeson, base, bytestring, stdenv, text
, uri-bytestring
}:
mkDerivation {
  pname = "uri-bytestring-aeson";
  version = "0.1.0.7";
  sha256 = "7e90b5eb1c65a83461e127a27ce635f2f8279eb0d0cb14823831b6dfb503ef9b";
  libraryHaskellDepends = [
    aeson base bytestring text uri-bytestring
  ];
  homepage = "https://github.com/reactormonk/uri-bytestring-aeson";
  description = "Aeson instances for URI Bytestring";
  license = stdenv.lib.licenses.bsd3;
}
