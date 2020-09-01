# Applies a list of overlays to the haskell package set rather than the entire
# nixpkgs, removing five levels of unsightly indentation.
{ overlays, ghcVer }:
self: super:
let
  inherit (super.lib) foldr composeExtensions;
  foldExtensions = foldr composeExtensions (_: _: {});
in {
  haskell = super.haskell // {
    packages = super.haskell.packages // {
      # overriding haskellPackages can produce surprising behaviour when
      # multiple overrides are applied. We need to remember to include previous
      # overrides in our overriding.
      # https://github.com/NixOS/nixpkgs/issues/26561#issuecomment-354862897
      "${ghcVer}" = super.haskell.packages."${ghcVer}".override (old: {
        overrides = composeExtensions
                      (old.overrides or (_: _: {}))
                      (foldExtensions (builtins.map (f: f { nixpkgs = self; }) overlays));
      });
    };
  };
}
