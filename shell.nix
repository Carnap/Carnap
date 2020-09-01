args@{ghcjs ? false, hls ? !ghcjs, ...}:
let
  importArgs = removeAttrs (args // { inherit hls; }) ["ghcjs"];
  def = import ./default.nix importArgs;
  inherit (def) ghcShell ghcjsShell;
in
if ghcjs then ghcjsShell else ghcShell
