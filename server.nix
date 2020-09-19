{ client, persistent, withHoogle ? true, profiling ? false }:
{ nixpkgs }:
let
  inherit (nixpkgs.haskell.lib)
    disableSharedExecutables
    doJailbreak
    dontCheck
    justStaticExecutables
    overrideSrc
    overrideCabal
    withGitignore;
in
newpkgs: oldpkgs: {
  # multiple issues: grumpy about haskell-src-exts versions
  # also, cabal-jailbreak does not erase bounds for feature-gated dependencies ;-;
  # I want to kill it 😭
  diagrams-builder = doJailbreak oldpkgs.diagrams-builder;
  # fix build of diagrams-builder by downgrading to 1.4.x
  diagrams-postscript = doJailbreak (oldpkgs.callHackage "diagrams-postscript" "1.4.1" { });

  # downgrade to 1.8.x because yesod-auth-oauth2 has not fixed support for
  # newer versions in any *released* version yet
  hoauth2 = oldpkgs.callHackage "hoauth2" "1.8.9" { };

  # update to fix a possible security bug: https://github.com/thoughtbot/yesod-auth-oauth2/issues/132
  yesod-auth-oauth2 = oldpkgs.callHackageDirect {
    pkg = "yesod-auth-oauth2";
    ver = "0.6.1.3";
    sha256 = "1bikn9kfw6mrsais4z1nk07aa7i7hyrcs411kbbfgc7n74k6sd5b";
  } { };

  # failing tests on macOS for some reason:
  # https://github.com/ubc-carnap-team/Carnap/runs/1074093219?check_suite_focus=true
  tz = dontCheck oldpkgs.tz;

  # Use the version from https://github.com/yesodweb/persistent/pull/1106
  # using overrideSrc to maintain dependency relations and nix's fixes/overrides for these
  persistent = overrideSrc oldpkgs.persistent { src = (persistent + "/persistent"); };
  persistent-sqlite = overrideSrc oldpkgs.persistent-sqlite { src = (persistent + "/persistent-sqlite"); };
  # this one we have to recreate from scratch anyway because they added a dependency
  persistent-postgresql = dontCheck (oldpkgs.callCabal2nix "persistent-postgresql" (persistent + "/persistent-postgresql") { });
  persistent-template = overrideSrc oldpkgs.persistent-template { src = (persistent + "/persistent-template"); };
  persistent-qq = overrideSrc oldpkgs.persistent-qq { src = (persistent + "/persistent-qq"); };
  persistent-test = overrideSrc oldpkgs.persistent-test { src = (persistent + "/persistent-test"); };
  # too tight an upper version bound on persistent
  yesod-persistent = doJailbreak oldpkgs.yesod-persistent;
  yesod-auth = doJailbreak oldpkgs.yesod-auth;

  # ghcjs-dom-0.2.4.0 (released 2016)
  # using `ghc` native dependencies
  # currently broken: ghcjs-dom needs to be updated to a newer
  # version such that it uses a modern webkitgtk
  # ghcjs-dom = oldpkgs.callPackage ./nix/ghcjs-dom.nix { };

  # they wrote a spec that calls out to Google. It does not work in a nix
  # builder.
  oidc-client = dontCheck oldpkgs.oidc-client;

  # lti13 and yesod-auth-lti13 are not in nixpkgs yet
  lti13 = oldpkgs.callHackageDirect {
    pkg = "lti13";
    ver = "0.1.2.1";
    sha256 = "14fxdjv8s9l2j1kxhryqjjcsyqb0ccb5f2ccq553d34xgi8qlzvr";
  } { };
  yesod-auth-lti13 = oldpkgs.callHackageDirect {
    pkg = "yesod-auth-lti13";
    ver = "0.1.2.1";
    sha256 = "0xm5cgccxb96rdyyqz5cjhi318f8nl3zxz7bg4k2p80mksg3ph10";
  } { };

  # dontCheck: https://github.com/gleachkr/Carnap/issues/123
  Carnap        = withGitignore
      (dontCheck (oldpkgs.callPackage ./Carnap/Carnap.nix { }));
  Carnap-Client = withGitignore
      (oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { });

  # for client development with ghc
  # Carnap-GHCJS  = withGitignore
  #    (oldpkgs.callPackage ./Carnap-GHCJS/Carnap-GHCJS.nix { });

  Carnap-Server = justStaticExecutables (withGitignore ((overrideCabal
    (oldpkgs.callCabal2nix "Carnap-Server" ./Carnap-Server { })
    (old: let book = ./Carnap-Book; in {
      preConfigure = ''
        mkdir -p $out/share
        echo ":: Copying Carnap-Server data"
        cp -r ${book} $out/share/book

        echo ":: Copying js in $(pwd)"
        find static/ghcjs/allactions/ -type l -delete
        cp ${client.out}/bin/AllActions.jsexe/all.js static/ghcjs/allactions/
        cp ${client.out}/bin/AllActions.jsexe/out.js static/ghcjs/allactions/
        cp ${client.out}/bin/AllActions.jsexe/lib.js static/ghcjs/allactions/
        cp ${client.out}/bin/AllActions.jsexe/runmain.js static/ghcjs/allactions/
        echo ":: Adding a universal settings file"
        cp config/settings-example.yml config/settings.yml
        cp -r {config,static} $out/share
        cat config/settings.yml
        '';

      enableExecutableProfiling = profiling;
      enableLibraryProfiling = profiling;
      buildDepends = [ book client ];
      executableSystemDepends = [ nixpkgs.diagrams-builder ];

      isExecutable = true;
      # Carnap-Server has no tests/they are broken
      doCheck = false;
      # remove once updated past ghc865
      # https://github.com/haskell/haddock/issues/979 (additionally disabled by
      # justStaticExecutables)
      doHaddock = false;
    })).overrideAttrs (drv: {
      # inspired by
      # https://github.com/NixOS/nixpkgs/blob/91340ae/pkgs/development/tools/pandoc/default.nix
      # reduce closure size by deleting references to the pandoc binary. pandoc
      # depends transitively on all installed haskell packages.  Bad for docker
      # image size (4GB+).
      disallowedReferences = with newpkgs; [
        warp
        yesod-core
        pandoc
        pandoc-types
        HTTP
        tzdata
      ];
      postInstall = with newpkgs; ''
        echo 'deleting reference to stuff with bins'
        remove-references-to \
          -t ${warp} \
          $out/bin/Carnap-Server
        remove-references-to \
          -t ${yesod-core} \
          $out/bin/Carnap-Server
        remove-references-to \
          -t ${pandoc} \
          $out/bin/Carnap-Server
        remove-references-to \
          -t ${pandoc-types} \
          $out/bin/Carnap-Server
        remove-references-to \
          -t ${HTTP} \
          $out/bin/Carnap-Server
        remove-references-to \
          -t ${tzdata} \
          $out/bin/Carnap-Server
      '';
    })));
}
