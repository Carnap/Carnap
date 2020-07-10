{ ghcjs ? "ghcjs",
  snapshot ? "lts-12.16",
}:
let
  stackage = import (fetchTarball {
    url = "https://stackage.serokell.io/ad0kwmbwynr9hk0g2xl9jc0cxnhjvl2f-stackage/default.nix.tar.gz";
    sha256 = "1imf2h1brpgpl5rfbyr7iqh3xpqflcgdi7p6g0nzx022yyrg0m91";
  });
  nixpkgs = import (builtins.fetchTarball {
        name = "nixpkgs-20.03-2020-06-28";
        url = "https://github.com/NixOS/nixpkgs/archive/f8248ab6d9e69ea9c07950d73d48807ec595e923.zip";
        sha256 = "009i9j6mbq6i481088jllblgdnci105b2q4mscprdawg3knlyahk";
      }) {
        overlays = [
          # adds pkgs.haskell.packages."${snapshot}"
          stackage."${snapshot}"
          (import ./client.nix { inherit ghcjs; })
          (import ./server.nix { inherit ghcjs snapshot; })
        ];
      };
  in {
    inherit (nixpkgs) haskell;
    client = nixpkgs.haskell.packages."${ghcjs}".Carnap-GHCJS;
    server = nixpkgs.haskell.packages."${snapshot}".Carnap-Server;

  }
