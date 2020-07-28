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
        ln -sf ${server.out}/share/* /data/
        Carnap-Server
        '';
  in {
    inherit server nixpkgs;

    docker = buildImage {
      name = "Carnap";
      tag = "latest";

      # no base image, make a minimized image
      contents = [ dockerEntrypoint nixpkgs.runtimeShellPackage server ];
      runAsRoot = ''
        #!${nixpkgs.runtimeShell}
        echo runAsRoot::
        mkdir -p /data
      '';

      config = {
        Cmd = [ dockerEntrypoint ];
        WorkingDir = "/data";
        Volumes = {
          "/data" = {};
        };
      };
    };
  }
