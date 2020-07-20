{}:
self: super:
  let
    gitignoreSrc = super.fetchFromGitHub {
      owner = "hercules-ci";
      repo = "gitignore";
      rev = "647d0821b590ee96056f4593640534542d8700e5";
      sha256 = "sha256:0ks37vclz2jww9q0fvkk9jyhscw0ial8yx2fpakra994dm12yy1d";
    };
  in {
    lib = super.lib // {
      inherit (import gitignoreSrc { inherit (super) lib; }) gitignoreSource;
    };
  }
