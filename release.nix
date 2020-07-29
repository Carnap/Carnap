{ hasKvm ? true }:
  let inherit (import ./default.nix {}) client server nixpkgs;
      overrideSet = f: set: set // (f set);

      # a hack to run the initial part of the docker build in software
      # emulation if kvm is not available
      # From: https://github.com/Gosha/tautulli-anidb-scrobbler/commit/65059835e565715308b4fc743120ba4fb56efe5c
      buildImage = if hasKvm then
        nixpkgs.dockerTools.buildImage
      else
        (nixpkgs.callPackage (nixpkgs.path + "/pkgs/build-support/docker") {
          vmTools = overrideSet
              (old: {
                # delete the requirement on the kvm feature
                runInLinuxVM = drv: nixpkgs.lib.overrideDerivation (old.runInLinuxVM drv) (_: {
                  requiredSystemFeatures = [ ];
                });
              })
              (nixpkgs.callPackage (nixpkgs.path + "/pkgs/build-support/vm") {
                pkgs = nixpkgs // { qemu_kvm = nixpkgs.callPackage ./nix/wrapped-qemu.nix { }; };
              });
        }).buildImage;

      dockerEntrypoint = nixpkgs.writeScriptBin "entrypoint.sh" ''
        #!${nixpkgs.runtimeShell}
        # this all needs to be mutable because yesod + diagrams-builder put
        # stuff dynamically under every single one of our "static" directories
        # >:(
        cp -r ${server.out}/share/* /data/
        mkdir -p /data/book/cache
        mkdir -p /data/data
        exec Carnap-Server
        '';
  in {
    inherit server nixpkgs;

    docker = buildImage {
      name = "Carnap";
      tag = "latest";

      # no base image, make a minimized image
      contents = [
        dockerEntrypoint
        nixpkgs.coreutils
        nixpkgs.runtimeShellPackage
        server
      ];
      runAsRoot = ''
        #!${nixpkgs.runtimeShell}
        echo runAsRoot::
        mkdir -p /data
      '';

      config = {
        Cmd = [ "entrypoint.sh" ];
        WorkingDir = "/data";
        Env = [
          "DATAROOT=/data/data"
          "BOOKROOT=/data/book/"
        ];
        ExposedPorts = {
          "3000" = {};
        };
        Volumes = {
          "/data" = {};
        };
      };
    };
  }
