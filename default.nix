{ ghcjs ? "ghcjs",
  ghc ? "ghc865",
}:
let
  nixpkgs = import (builtins.fetchTarball {
        name = "nixpkgs-20.03-2020-06-28";
        url = "https://github.com/NixOS/nixpkgs/archive/f8248ab6d9e69ea9c07950d73d48807ec595e923.zip";
        sha256 = "009i9j6mbq6i481088jllblgdnci105b2q4mscprdawg3knlyahk";
      }) {
        overlays = [
          (import ./client.nix { inherit ghcjs; })
          (import ./server.nix { inherit ghcjs ghc; })
        ];
      };
  in rec {
    inherit (nixpkgs) haskell;
    client = nixpkgs.haskell.packages."${ghcjs}".Carnap-GHCJS;
    server = nixpkgs.haskell.packages."${ghc}".Carnap-Server;
    shell  = nixpkgs.haskell.packages."${ghc}".shellFor {
      withHoogle = true;
      packages = p: [ client server ];
      buildInputs = with nixpkgs.haskell; [ packages.${ghc}.cabal-install packages.${ghcjs}.ghc ];
    };
  }
