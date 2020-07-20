{ ghcjsVer, ghcVer, withHoogle ? true }:
  self: super:
  let
    inherit (super.haskell.lib)
      overrideCabal
      dontCheck
      doJailbreak
      withGitignore;
    client-ghcjs = self.haskell.packages.${ghcjsVer}.Carnap-GHCJS;
  in {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${ghcVer}" = super.haskell.packages."${ghcVer}".override {
          overrides = newpkgs: oldpkgs: {
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
            glib = oldpkgs.callPackage ./nix/glib.nix { inherit (self) glib; };
            pango = oldpkgs.callPackage ./nix/pango.nix { inherit (self) pango; };
            cairo = oldpkgs.callPackage ./nix/cairo.nix { inherit (self) cairo; };

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

            Carnap-Server = withGitignore (overrideCabal
              (oldpkgs.callPackage ./Carnap-Server/Carnap-Server.nix { })
              (old: let book = ./Carnap-Book; in {
                preConfigure = ''
                  mkdir -p $out/share
                  echo ":: Installing ${book} in $out/share/Carnap-Book"
                  cp -r ${book} $out/share/Carnap-Book
                  echo ":: Copying static files"
                  cp -r static $out/share/static

                  echo ":: Symlinking js in $(pwd)"
                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/all.js $out/share/static/ghcjs/allactions/
                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/out.js $out/share/static/ghcjs/allactions/
                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/lib.js $out/share/static/ghcjs/allactions/
                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/runmain.js $out/share/static/ghcjs/allactions/
                  echo ":: Adding a universal settings file"
                  cp config/settings-example.yml config/settings.yml
                  sed -i "s#/var/lib/carnap/book/#$out/share/Carnap-Book/#" config/settings.yml
                  sed -i "s#_env:STATIC_DIR:static#_env:STATIC_DIR:$out/share/static#" config/settings.yml
                  cat config/settings.yml
                  '';
                extraLibraries = [ client-ghcjs ];
                buildDepends = [ book ];
                # Carnap-Server has no tests/they are broken
                doCheck = false;
                # remove once updated past ghc865
                # https://github.com/haskell/haddock/issues/979
                doHaddock = false;
              }));
          };
        };
      };
    };
  }
