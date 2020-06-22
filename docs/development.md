## Developing Carnap

Carnap consists of two components: a native Haskell project, Carnap-Server
managed using `stack`, and a client side codebase including GHCJS, managed with
`cabal`.

## Setup with Nix

The easiest way to set up your environment for building Carnap is to use `nix`.
It must be noted that this method is not 'correct' (theoretically we should
write a bunch of Nix script and use isolated environments rather than doing it
globally but this is not ready yet).

Install it from [the website](https://nixos.org/download.html) with
```
$ sh <(curl https://nixos.org/nix/install) --no-daemon --no-channel-add
$ # Follow the instructions output by the installer.
$ nix-channel --add https://nixos.org/channels/nixos-20.03 nixpkgs
$ nix-channel --update
```

Note: As of 2020-06-21, the ghcjs package in nixpkgs-unstable is broken. The
version in nixos-20.03 works, which is why we do this.

Next, install Haskell software (get rid of your existing ones first):
```
$ nix-env -iA nixpkgs.haskell.compiler.ghcjs nixpkgs.stack nixpkgs.cabal-install
```

## Building Carnap front end (WIP)

```
$ make build-client
```

## Building Carnap-Server in development

```
$ make build-server-dev
```

## Running Carnap-Server in development

```
$ make run-server
```

# Common Issues

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
