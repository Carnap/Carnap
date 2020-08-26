args@{ghcjs ? false, hls ? !ghcjs, ...}:
let
  importArgs = args // { inherit hls; };
  def = import ./default.nix importArgs;
  inherit (def) ghcShell ghcjsShell;
in
if ghcjs then ghcjsShell else ghcShell
