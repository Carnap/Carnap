{ ghcjs ? "ghcjs", ghc ? "lts-12.16" }:
  self: super:
  let overrideCabal = super.haskell.lib.overrideCabal;
      dontCheck = super.haskell.lib.dontCheck;
      doJailbreak = super.haskell.lib.doJailbreak;
      client-ghcjs = self.haskell.packages.${ghcjs}.Carnap-GHCJS;
  in {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${ghc}" = super.haskell.packages."${ghc}".override {
          overrides = newpkgs: oldpkgs: {
            # broken dependencies in nixpkgs :(
            haskell-src-exts-simple = doJailbreak (oldpkgs.haskell-src-exts-simple);
            diagrams-builder = doJailbreak (oldpkgs.diagrams-builder);

            Carnap        = oldpkgs.callPackage ./Carnap/Carnap.nix { };
            Carnap-Client = oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { };
            Carnap-Server = overrideCabal
                              (oldpkgs.callPackage ./Carnap-Server/Carnap-Server.nix { })
                              (old: {
                                preConfigure = ''
                                  echo "symlinking js in $(pwd)"
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/all.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/out.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/lib.js static/ghcjs/allactions/
                                  '';
                                extraLibraries = [ client-ghcjs ];
                              });
          };
        };
      };
    };
  }
