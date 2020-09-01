{ mkDerivation, aeson, base, blaze-html, bytestring, Carnap
, Carnap-Client, case-insensitive, classy-prelude
, classy-prelude-conduit, classy-prelude-yesod, conduit, containers
, data-default, diagrams, diagrams-builder, diagrams-lib
, diagrams-svg, directory, fast-logger, file-embed, filepath
, hashable, hspec, http-conduit, lens, linear, lucid, monad-control
, monad-logger, mtl, pandoc, pandoc-types, persistent
, persistent-postgresql, persistent-sqlite, persistent-template
, random, resourcet, safe, shakespeare, split, stdenv, svg-builder
, template-haskell, text, th-utilities, time, transformers, tz
, tzdata, unordered-containers, vector, wai, wai-cors, wai-extra
, wai-logger, warp, yaml, yesod, yesod-auth, yesod-auth-oauth2
, yesod-core, yesod-form, yesod-markdown, yesod-static, yesod-test
}:
mkDerivation {
  pname = "Carnap-Server";
  version = "0.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base blaze-html bytestring Carnap Carnap-Client
    case-insensitive classy-prelude classy-prelude-conduit
    classy-prelude-yesod conduit containers data-default diagrams
    diagrams-builder diagrams-lib diagrams-svg directory fast-logger
    file-embed filepath hashable http-conduit lens linear lucid
    monad-control monad-logger mtl pandoc pandoc-types persistent
    persistent-postgresql persistent-sqlite persistent-template random
    safe shakespeare split svg-builder template-haskell text
    th-utilities time transformers tz tzdata unordered-containers
    vector wai wai-cors wai-extra wai-logger warp yaml yesod yesod-auth
    yesod-auth-oauth2 yesod-core yesod-form yesod-markdown yesod-static
  ];
  executableHaskellDepends = [ base ];
  testHaskellDepends = [
    aeson base classy-prelude classy-prelude-yesod hspec monad-logger
    persistent persistent-postgresql resourcet shakespeare transformers
    yesod yesod-core yesod-test
  ];
  license = "unknown";
  hydraPlatforms = stdenv.lib.platforms.none;
}
