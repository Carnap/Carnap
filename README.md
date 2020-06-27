# Carnap

Carnap is an open source logic textbook and homework system.

## Developing Carnap

Carnap consists of two components: a native Haskell project, Carnap-Server
managed using `stack`, and a client side codebase including GHCJS, managed with
`cabal`.

### Setup with Nix

The easiest way to set up your environment for building Carnap is to use `nix`.
It must be noted that this method is not 'correct' (theoretically we should
write a bunch of Nix script and use isolated environments rather than doing it
globally but this is not ready yet).

Install it from [the website](https://nixos.org/download.html) with
```
$ sh <(curl -L https://nixos.org/nix/install) --no-daemon --no-channel-add
$ # Follow the instructions output by the installer.
$ nix-channel --add https://nixos.org/channels/nixos-20.03 nixpkgs
$ nix-channel --update
```

Note: As of 2020-06-21, the ghcjs package in nixpkgs-unstable is broken. The
version in nixos-20.03 works, which is why we do this.

Next, install Haskell software (get rid of your existing ones first):
```
$ nix-env -iA nixpkgs.haskell.compiler.ghcjs nixpkgs.haskell.compiler.ghc865 nixpkgs.stack nixpkgs.cabal-install
```

### Building Carnap front end

*NOTE*: This takes about 10GB of memory to do. If you don't have that amount
free, consider setting up a swap file or closing some programs.

Also, note that we do not automatically run `cabal update` for you after the
initial run.

```
$ make build-client
```

### Building Carnap-Server in development

This will automatically build the client then the server. You can also run
`make all` or just `make`.

```
$ make build-server-dev
```

### Running Carnap-Server in development

```
$ make run-server
```

### Building Carnap-Server in production

```
$ make build-server
```

### Common Issues

General build weirdness can often be resolved with `make clean` which deletes
all the intermediate results and forces a full rebuild next time.

#### Missing `ghcjs_allactions_*.js`

```
Carnap-Server> [21 of 38] Compiling Handler.Info
Carnap-Server>
Carnap-Server> /home/lf/dev/Carnap/Carnap-Server/Handler/Info.hs:13:29: error:
Carnap-Server>     Variable not in scope: ghcjs_allactions_lib_js :: Route Static
Carnap-Server>    |
Carnap-Server> 13 |         addScript $ StaticR ghcjs_allactions_lib_js
Carnap-Server>    |                             ^^^^^^^^^^^^^^^^^^^^^^^
Carnap-Server>
Carnap-Server> /home/lf/dev/Carnap/Carnap-Server/Handler/Info.hs:14:29: error:
Carnap-Server>     Variable not in scope: ghcjs_allactions_out_js :: Route Static
Carnap-Server>    |
Carnap-Server> 14 |         addScript $ StaticR ghcjs_allactions_out_js
Carnap-Server>    |                             ^^^^^^^^^^^^^^^^^^^^^^^
Carnap-Server>
Carnap-Server> /home/lf/dev/Carnap/Carnap-Server/Handler/Info.hs:24:29: error:
Carnap-Server>     Variable not in scope: ghcjs_allactions_runmain_js :: Route Static
Carnap-Server>    |
Carnap-Server> 24 |         addScript $ StaticR ghcjs_allactions_runmain_js
Carnap-Server>    |                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

Delete `Carnap-Server/.stack-work` or run `make clean` and rebuild. Client JS
was not properly symlinked.
