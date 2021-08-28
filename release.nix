{}:
let inherit (import ./default.nix { }) client server nixpkgs;

  dockerEntrypoint = nixpkgs.writeScriptBin "entrypoint.sh" ''
    #!${nixpkgs.runtimeShell}
    # this all needs to be mutable because yesod put stuff dynamically under
    # every single one of our "static" directories >:(
    cp -r ${server.out}/share/* /data/
    mkdir -p /data/book/cache
    mkdir -p /data/data
    exec ${server.out}/bin/Carnap-Server
  '';

  inherit (nixpkgs.lib) pathIsGitRepo commitIdFromGitRepo;

  maybeGitRevision = let
    gitdir = "${toString ./.}/.git";
  in if pathIsGitRepo gitdir
    then commitIdFromGitRepo gitdir
    else "UNKNOWN";
in
{
  inherit server nixpkgs maybeGitRevision;

  docker = nixpkgs.dockerTools.buildImage {
    name = "Carnap";
    tag = "latest";

    # we probably don't have any symlinks but if we do, they are not
    # problematic, and this may save space
    keepContentsDirlinks = true;

    # no base image, make a minimized image
    contents = [
      dockerEntrypoint
      nixpkgs.coreutils
      nixpkgs.runtimeShellPackage
      nixpkgs.cacert # for connecting out to google dot com for oauth
    ];

    # run unprivileged with the current directory as the root of the image
    extraCommands = ''
      #!${nixpkgs.runtimeShell}
      mkdir -p data
    '';

    config = {
      Cmd = [ "entrypoint.sh" ];
      WorkingDir = "/data";
      Env = [
        "DATAROOT=/data/data"
        "BOOKROOT=/data/book/"
      ];
      ExposedPorts = {
        "3000" = { };
      };
      Volumes = {
        "/data" = { };
      };
      Labels = {
        "io.carnap.git.revision" = maybeGitRevision;
      };
    };
  };
}
