{ ghcjsVer ? "ghcjs",
  ghcVer ? "ghc865",
  profiling ? false,
  useHie ? false,
}:
let
  optionalOverlay = cond: ovl: (if cond then ovl else _: _: {});
  all-hies = builtins.fetchTarball {
    url = "https://github.com/infinisil/all-hies/tarball/09ba836904fa290b5e37d5403150ea0c921661fb";
    sha256 = "0qbjqv1fkhkx1cffqybz1mfks1jphh0vh3zd8ad2qd6lch4gyys4";
  };

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
        (optionalOverlay useHie (import all-hies {}).overlay)
        (import ./nix/gitignore.nix { })
        (import ./nix/compose-haskell-overlays.nix {
          inherit ghcVer;
          overlays = [
            (import ./server.nix { inherit ghcjsVer profiling; })
          ];
        })
        (import ./nix/compose-haskell-overlays.nix {
          ghcVer = ghcjsVer;
          overlays = [
            (import ./client.nix { })
          ];
        })
      ];
    };

  inherit (nixpkgs) lib;

  devtools = with nixpkgs.haskell.packages."${ghcVer}"; ([
    Cabal
    cabal-install
    ghcid
    hasktags
    yesod-bin
  ] ++ (lib.optional useHie hie)
  ) ++ (with nixpkgs; [
    cabal2nix
  ]);

  in rec {
    inherit nixpkgs;
    client = nixpkgs.haskell.packages."${ghcjsVer}".Carnap-GHCJS;
    server = nixpkgs.haskell.packages."${ghcVer}".Carnap-Server;

    # a ghc-based shell for development of Carnap and Carnap-Server
    # Carnap-GHCJS currently broken on ghc, see `server.nix` for details
    ghcShell = nixpkgs.haskell.packages."${ghcVer}".shellFor {
      packages = p: [ p.Carnap p.Carnap-Client p.Carnap-Server ];
      withHoogle = true;
      buildInputs = devtools;
    };

    ghcjsShell = nixpkgs.haskell.packages."${ghcjsVer}".shellFor {
      packages = p: [ p.Carnap p.Carnap-Client p.Carnap-GHCJS ];
      withHoogle = true;
      buildInputs = devtools;
    };
  }
