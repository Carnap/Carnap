{}:
  let inherit (import ./default.nix {}) client server nixpkgs;
      inherit (nixpkgs.dockerTools) buildImage;
  in {
    inherit server;

    docker = buildImage {
      name = "Carnap";
      tag = "latest";

      # no base image, make a minimized image
      contents = [ server ];
      runAsRoot = ''
        #!${nixpkgs.runtimeShell}
        mkdir -p /data
        cp -r ${server.out}/share/* /data
      '';

      config = {
        Cmd = [ "/bin/Carnap-Server" ];
        WorkingDir = "/data";
        Volumes = {
          "/data" = {};
        };
      };
    };
  }
