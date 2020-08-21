args@{ghcjs ? false, ...}:
let
  inherit (import ./default.nix (removeAttrs args [ "ghcjs" ])) ghcShell ghcjsShell;
in
if ghcjs then ghcjsShell else ghcShell
