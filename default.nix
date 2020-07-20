{ ghcjsVer ? "ghcjs",
  ghcVer ? "ghc865",
}:
let
  nixpkgs = import (builtins.fetchTarball {
        name   = "nixpkgs-20.03-2020-06-28";
        url    = "https://github.com/NixOS/nixpkgs/archive/f8248ab6d9e69ea9c07950d73d48807ec595e923.tar.gz";
        sha256 = "009i9j6mbq6i481088jllblgdnci105b2q4mscprdawg3knlyahk";
      }) {
        config = {
          # yes, packages are broken, but we fix them ;-)
          allowBroken = true;
        };
        overlays = [
          (import ./nix/gitignore.nix { })
          (import ./client.nix { inherit ghcjsVer; })
          (import ./server.nix { inherit ghcjsVer ghcVer; })
        ];
      };

  workOnMulti = import ./nix/work-on-multi.nix {
    inherit nixpkgs;
    # put whatever tools you want in the shell environments here
    generalDevTools = _: {
      inherit (nixpkgs) cabal2nix;
      inherit (nixpkgs.haskell.packages."${ghcVer}")
        Cabal
        cabal-install
        ghcid
        hasktags
        yesod-bin;
    };
  };

  in rec {
    inherit nixpkgs;
    client = nixpkgs.haskell.packages."${ghcjsVer}".Carnap-GHCJS;
    server = nixpkgs.haskell.packages."${ghcVer}".Carnap-Server;

    # a ghc-based shell for development of Carnap and Carnap-Server
    # Carnap-GHCJS currently broken on ghc, see `server.nix` for details
    ghcShell = workOnMulti {
      envPackages = [
        "Carnap"
        "Carnap-Server"
        "Carnap-Client"
        # "Carnap-GHCJS"
      ];
      env = with nixpkgs.haskell.packages."${ghcVer}"; {
        # enable hoogle in the environment
        ghc = ghc.override {
          override = self: super: {
            withPackages = super.ghc.withHoogle;
          };
        };
        inherit Carnap Carnap-Client Carnap-Server /* Carnap-GHCJS */ mkDerivation;
      };
    };

    ghcjsShell = workOnMulti {
      envPackages = [
        "Carnap"
        "Carnap-Client"
        "Carnap-GHCJS"
      ];
      env = with nixpkgs.haskell.packages."${ghcjsVer}"; {
        # enable hoogle in the environment
        ghc = ghc.override {
          override = self: super: {
            withPackages = super.ghc.withHoogle;
          };
        };
        inherit Carnap Carnap-Client Carnap-GHCJS mkDerivation;
      };
    };
  }
