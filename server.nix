{ ghcjsVer, withHoogle ? true, profiling ? false }:
{ nixpkgs }:
let
  inherit (nixpkgs.haskell.lib)
    overrideCabal
    dontCheck
    disableSharedExecutables
    doJailbreak
    justStaticExecutables
    withGitignore;
  client-ghcjs = nixpkgs.haskell.packages.${ghcjsVer}.Carnap-GHCJS;
in
newpkgs: oldpkgs: {
  # broken dependencies in nixpkgs :(
  haskell-src-exts-simple = doJailbreak oldpkgs.haskell-src-exts-simple;
  diagrams-builder = doJailbreak oldpkgs.diagrams-builder;

  # updates pango, glib, cairo to a version including
  # https://github.com/gtk2hs/gtk2hs/commit/1cf2f9bff2427d39986e32880d1383cfff49ab0e
  # remove once nixpkgs.haskell.packages.ghc865.glib version >= 0.13.8.1
  # i.e. most likely when we update past nixpkgs-20.03 (pending nixpkgs
  # unstable having a working ghcjs) as pango-0.13.8.1 is in unstable
  # already
  # I checked this with:
  # $ nix-instantiate '<nixpkgs-unstable>' -A haskell.packages.ghc865.pango
  # /nix/store/aqvkx9yd2s5m0svki3fr84klq6fyw6dw-pango-0.13.8.1.drv
  glib = oldpkgs.callPackage ./nix/glib.nix { inherit (nixpkgs) glib; };
  pango = oldpkgs.callPackage ./nix/pango.nix { inherit (nixpkgs) pango; };
  cairo = oldpkgs.callPackage ./nix/cairo.nix { inherit (nixpkgs) cairo; };

  # ghcjs-dom-0.2.4.0 (released 2016)
  # using `ghc` native dependencies
  # currently broken: ghcjs-dom needs to be updated to a newer
  # version such that it uses a modern webkitgtk
  # ghcjs-dom = oldpkgs.callPackage ./nix/ghcjs-dom.nix { };

  # dontCheck: https://github.com/gleachkr/Carnap/issues/123
  Carnap        = withGitignore
      (dontCheck (oldpkgs.callPackage ./Carnap/Carnap.nix { }));
  Carnap-Client = withGitignore
      (oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { });

  # for client development with ghc
  # Carnap-GHCJS  = withGitignore
  #    (oldpkgs.callPackage ./Carnap-GHCJS/Carnap-GHCJS.nix { });

  Carnap-Server = justStaticExecutables (withGitignore ((overrideCabal
    (oldpkgs.callPackage ./Carnap-Server/Carnap-Server.nix { })
    (old: let book = ./Carnap-Book; in {
      preConfigure = ''
        mkdir -p $out/share
        echo ":: Copying Carnap-Server data"
        cp -r ${book} $out/share/book

        echo ":: Copying js in $(pwd)"
        find static/ghcjs/allactions/ -type l -delete
        cp ${client-ghcjs.out}/bin/AllActions.jsexe/all.js static/ghcjs/allactions/
        cp ${client-ghcjs.out}/bin/AllActions.jsexe/out.js static/ghcjs/allactions/
        cp ${client-ghcjs.out}/bin/AllActions.jsexe/lib.js static/ghcjs/allactions/
        cp ${client-ghcjs.out}/bin/AllActions.jsexe/runmain.js static/ghcjs/allactions/
        echo ":: Adding a universal settings file"
        cp config/settings-example.yml config/settings.yml
        cp -r {config,static} $out/share
        cat config/settings.yml
        '';

      extraLibraries = [ client-ghcjs ];
      enableExecutableProfiling = profiling;
      enableLibraryProfiling = profiling;
      buildDepends = [ book ];
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
