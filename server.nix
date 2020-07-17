{ ghcjsVer, ghcVer, withHoogle ? true }:
  self: super:
  let overrideCabal = super.haskell.lib.overrideCabal;
      dontCheck = super.haskell.lib.dontCheck;
      doJailbreak = super.haskell.lib.doJailbreak;
      client-ghcjs = self.haskell.packages.${ghcjsVer}.Carnap-GHCJS;
  in {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${ghcVer}" = super.haskell.packages."${ghcVer}".override {
          overrides = newpkgs: oldpkgs: {
            # broken dependencies in nixpkgs :(
            haskell-src-exts-simple = doJailbreak oldpkgs.haskell-src-exts-simple;
            diagrams-builder = doJailbreak oldpkgs.diagrams-builder;

            # ghcjs-dom-0.2.4.0 (released 2016)
            # using `ghc` native dependencies
            # currently broken: ghcjs-dom needs to be updated to a newer
            # version such that it uses a modern webkitgtk
            # ghcjs-dom = oldpkgs.callPackage ./nix/ghcjs-dom.nix { };

            # dontCheck: https://github.com/gleachkr/Carnap/issues/123
            Carnap        = dontCheck (oldpkgs.callPackage ./Carnap/Carnap.nix { });
            Carnap-Client = oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { };
            # for client development with ghc
            # Carnap-GHCJS  = oldpkgs.callPackage ./Carnap-GHCJS/Carnap-GHCJS.nix { };
            Carnap-Server = overrideCabal
                              (oldpkgs.callPackage ./Carnap-Server/Carnap-Server.nix { })
                              (old: {
                                preConfigure = ''
                                  echo "symlinking js in $(pwd)"
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/all.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/out.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/lib.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/runmain.js static/ghcjs/allactions/
                                  '';
                                extraLibraries = [ client-ghcjs ];
                                # Carnap-Server has no tests/they are broken
                                doCheck = false;
                                # remove once updated past ghc865
                                # https://github.com/haskell/haddock/issues/979
                                doHaddock = false;
                              });
          };
        };
      };
    };
  }
