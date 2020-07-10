{ mkDerivation, aeson, base, bytestring, Carnap, containers, parsec
, stdenv, text
}:
mkDerivation {
  pname = "Carnap-Client";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    aeson base bytestring Carnap containers parsec text
  ];
  description = "Shared Components for client-server Carnap applications";
  license = stdenv.lib.licenses.gpl3;
}
