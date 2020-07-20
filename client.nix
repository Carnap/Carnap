{ ghcjsVer ? "ghcjs" }:
  self: super:
  let inherit (super.haskell.lib) dontCheck withGitignore;
  in {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${ghcjsVer}" = super.haskell.packages."${ghcjsVer}".override {
          overrides = newpkgs: oldpkgs: {
            # most tests are broken on ghcjs even if packages themselves work
            # we also disable library profiling for compile perf
            mkDerivation = args: oldpkgs.mkDerivation (args // {
              doCheck = false;
              enableLibraryProfiling = false;
            });

            # nixpkgs has overridden this one extra spicily to test on !i686
            # which ironically includes us, in spite of us blocking tests.
            # Override it harder.
            diagrams-lib = dontCheck oldpkgs.diagrams-lib;

            # ghcjs-dom-0.2.4.0 (released 2016)
            ghcjs-dom = oldpkgs.callPackage ./nix/ghcjs-dom-ghcjs.nix { };

            Carnap = withGitignore (oldpkgs.callPackage ./Carnap/Carnap.nix { });

            Carnap-Client = withGitignore
                (oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { });

            Carnap-GHCJS = withGitignore
                (oldpkgs.callPackage ./Carnap-GHCJS/Carnap-GHCJS.nix { });
          };
        };
      };
    };
  }
