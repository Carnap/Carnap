{ ghcjs ? "ghcjs", snapshot ? "lts-12.16" }:
  self: super:
  let overrideCabal = super.haskell.lib.overrideCabal;
      dontCheck = super.haskell.lib.dontCheck;
      doJailbreak = super.haskell.lib.doJailbreak;
      client-ghcjs = self.haskell.packages.${ghcjs}.Carnap-GHCJS;
  in {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${snapshot}" = super.haskell.packages."${snapshot}".override {
          overrides = newpkgs: oldpkgs: {
            # it's broken in our nixpkgs I guess??
            # haskell-src-exts-simple = doJailbreak (oldpkgs.haskell-src-exts-simple);
            # diagrams-builder = doJailbreak (oldpkgs.diagrams-builder);

            # tests are broken
            alex = dontCheck (oldpkgs.alex);
            #bifunctors = dontCheck (oldpkgs.bifunctors);

            # the packages from extra-deps in stack.yaml, from hackage
            yesod-auth-oauth2    = oldpkgs.callPackage ./nix/yesod-auth-oauth2.nix { };
            yesod-markdown       = oldpkgs.callPackage ./nix/yesod-markdown.nix { };
            hoauth2              = oldpkgs.callPackage ./nix/hoauth2.nix { };
            uri-bytestring-aeson = oldpkgs.callPackage ./nix/uri-bytestring-aeson.nix { };

            Carnap        = oldpkgs.callPackage ./Carnap/Carnap.nix { };
            Carnap-Client = oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { };
            Carnap-Server = doJailbreak (overrideCabal
                              (oldpkgs.callPackage ./Carnap-Server/Carnap-Server.nix { })
                              (old: {
                                preConfigure = ''
                                  echo "symlinking js $(pwd)"
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/all.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/out.js static/ghcjs/allactions/
                                  ln -sf ${client-ghcjs.out}/bin/AllActions.jsexe/lib.js static/ghcjs/allactions/
                                  '';
                                extraLibraries = [ client-ghcjs ];
                              }));
          };
        };
      };
    };
  }
