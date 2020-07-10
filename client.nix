{ ghcjs ? "ghcjs" }:
  self: super:
  let dontCheck = super.haskell.lib.dontCheck;
  in {
    haskell = super.haskell // {
      packages = super.haskell.packages // {
        "${ghcjs}" = super.haskell.packages."${ghcjs}".override {
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

            # I have nixified the version of ghcjs-dom from 2017 we were using
            # This is terrible, but fixing it would require Carnap be ported to a newer one.
            ghcjs-dom = (oldpkgs.callPackage (builtins.fetchTarball {
              name = "ghcjs-dom-0.2.4.0";
              url = "https://github.com/lf-/ghcjs-dom/archive/f8748a7db0242121a24604720b65abb9aca6c299.tar.gz";
              sha256 = "1h975d0pn5xys61phmwms72jh6ar2p98a5qc7gsd61208flikh72";
            })) {};

            Carnap = oldpkgs.callPackage ./Carnap/Carnap.nix { };
            Carnap-Client = oldpkgs.callPackage ./Carnap-Client/Carnap-Client.nix { };
            Carnap-GHCJS = oldpkgs.callPackage ./Carnap-GHCJS/Carnap-GHCJS.nix { };
          };
        };
      };
    };
  }
