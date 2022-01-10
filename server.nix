{ client, truth-tree, persistent, withHoogle ? true, profiling ? false }:
{ nixpkgs }:
let
  inherit (nixpkgs.lib) gitignoreSource concatMapStrings;
  inherit (nixpkgs.haskell.lib)
    disableSharedExecutables
    disableLibraryProfiling
    doJailbreak
    dontCheck
    justStaticExecutables
    overrideSrc
    overrideCabal;
in
newpkgs: oldpkgs: {
  # failing tests on macOS for some reason:
  # https://github.com/ubc-carnap-team/Carnap/runs/1074093219?check_suite_focus=true
  tz = dontCheck oldpkgs.tz;

  # they wrote a spec that calls out to Google. It does not work in a nix
  # builder.
  oidc-client = dontCheck oldpkgs.oidc-client;

  # lti13 and yesod-auth-lti13 are not in all-hashes yet, 99% of the time, so
  # just manually pull them...
  #
  # Development overrides:
  # lti13 = oldpkgs.callCabal2nix "lti13" ../lti13/lti13 { };
  # yesod-auth-lti13 = oldpkgs.callCabal2nix "yesod-auth-lti13" ../lti13/yesod-auth-lti13 { };
  lti13 = oldpkgs.callHackageDirect {
    pkg = "lti13";
    ver = "0.2.0.3";
    sha256 = "0hwsrag4skck992hnzmj5n5iclbbrbwdwa5rxsrks8ins7jgrg1f";
  } { };
  yesod-auth-lti13 = oldpkgs.callHackageDirect {
    pkg = "yesod-auth-lti13";
    ver = "0.2.0.3";
    sha256 = "0mmhznyzjaqmbcgvcznab2sx5ghaxv66cxq07b8yimg61yfadbgb";
  } { };

  # dontCheck: https://github.com/gleachkr/Carnap/issues/123
  Carnap        = disableLibraryProfiling
                    (dontCheck (oldpkgs.callCabal2nix "Carnap" (gitignoreSource ./Carnap) { }));
  Carnap-Client = disableLibraryProfiling
                    (oldpkgs.callCabal2nix "Carnap-Client" (gitignoreSource ./Carnap-Client) { });

  Carnap-Server = justStaticExecutables ((overrideCabal
    (oldpkgs.callCabal2nix "Carnap-Server" (gitignoreSource ./Carnap-Server) { })
    (old: let book = ./Carnap-Book; in {
      preConfigure = ''
        mkdir -p $out/share
        echo ":: Copying Carnap-Server data"
        cp -r ${book} $out/share/book

        echo ":: Copying js in $(pwd)"
        find static/ghcjs/allactions/ -type l -delete
        # all.js seems to not be referenced so let's save 58MB
        # cp ${client.out}/bin/AllActions.jsexe/all.js static/ghcjs/allactions/
        cp ${client.out}/bin/AllActions.jsexe/out.js static/ghcjs/allactions/
        cp ${client.out}/bin/AllActions.jsexe/lib.js static/ghcjs/allactions/
        cp ${client.out}/bin/AllActions.jsexe/runmain.js static/ghcjs/allactions/

        find static/truth-tree -type l -delete
        cp ${truth-tree.out}/dist/lib.css static/truth-tree/
        cp ${truth-tree.out}/dist/lib.js  static/truth-tree/
        # delete the symlinks to the source maps
        rm -f static/truth-tree/lib.{css,js}.map

        echo ":: Adding a universal settings file"
        cp config/settings-example.yml config/settings.yml
        cp -r {config,static} $out/share
        cat config/settings.yml
        '';

      enableExecutableProfiling = profiling;
      enableLibraryProfiling = profiling;
      buildDepends = [ book client truth-tree ];

      isExecutable = true;
      # Carnap-Server has no tests/they are broken
      doCheck = false;
      # remove once updated past ghc865
      # https://github.com/haskell/haddock/issues/979 (additionally disabled by
      # justStaticExecutables)
      doHaddock = false;
    })).overrideAttrs (drv: rec {
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
          ${concatMapStrings (t: "-t ${t} ") disallowedReferences} \
          $out/bin/Carnap-Server
        '';
    }));
}
