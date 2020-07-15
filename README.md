# Carnap

Carnap is a web-based system for logic textbooks.

## Development

### General information

Nix is used to speed up builds and avoid having to compile dependencies,
instead using cached built versions from nixpkgs. It also makes it easy to
[Dockerize](https://nixos.org/nixpkgs/manual/#sec-pkgs-dockerTools) (see also
NixOps) and implement CI.

Carnap has a GHCJS (client side) and a GHC (server side) part.

Carnap-Server depends on the client side being available at `client-out` or
otherwise linked into its static folder.  This is accomplished automatically
when we are building Nix packages for production, but this dependency is not
automatically managed during development and you thus have to build the client
side JavaScript before building the server.

Nix does not support incremental package builds, so the suggested development
workflow is to use `cabal` in a shell. A `Makefile` has been provided to make
this easier.

### Nix setup

Install Nix with your *non-root* user account:

```
$ bash <(curl -L https://nixos.org/nix/install)
```

You can significantly speed up builds by using binaries for Carnap dependencies
from @lf-'s [Cachix](https://cachix.org/) instance. To use it:

```
$ # Install Cachix:
$ nix-env -iA cachix -f https://cachix.org/api/v1/install
$ # Use the Carnap Cachix
$ cachix use jade-carnap
```

Then build as normal.

### Build the front end

This builds the Carnap-GHCJS package under `ghcjs` along with its dependencies.
(note: takes about 9-10GB of RAM at the final linking stage)

```
$ nix-build -j4 -A client -o client-out
```

### Build Carnap-Server

This will also automatically build the client and any dependencies if
necessary.

```
$ nix-build -j4 -A server -o server-out
```

### Get a GHC based development shell

This requires a [client be built using Nix](#Build-the-front-end) if you want
to build Carnap-Server in this shell with Cabal.

Using `make` aliases:

```
$ make shell-ghc
[nix-shell:Carnap]$ make build-ghc
[nix-shell:Carnap]$ make run
```

Manually:

```
$ nix-shell -A ghcShell
[nix-shell:Carnap]$ cabal new-build -f dev all
[nix-shell:Carnap]$ cd Carnap-Server
[nix-shell:Carnap-Server]$ APPROOT="http://localhost:3000" DATAROOT="../dataroot" BOOKROOT="../Carnap-Book/" cabal run -f dev Carnap-Server
```

### Get a GHCJS based development shell

Using `make` aliases:

```
$ make shell-ghcjs
[nix-shell:~/dev/Carnap]$ make build-ghcjs
```

Manually:

```
$ nix-shell -A ghcjsShell
$ cabal --project-file=cabal-ghcjs.project --builddir=dist-ghcjs new-build all
```

## Maintainer information

### Pushing to Cachix

This will likely be obviated in the future by doing this step in CI.

```
$ nix-build -A server | cachix push jade-carnap
```

### Generate the `.nix` files in a subproject

For example:

```
$ cd Carnap-Client; cabal2nix . > Carnap-Client.nix
```

### Updating nixpkgs

`nixpkgs` is pinned in this project in order to ensure builds are reproducible.
It should be updated manually on occasion.

```
--- Get the latest version ---
» git ls-remote https://github.com/NixOS/nixpkgs nixos-20.03
1a92d0abfcdbafc5c6e2fdc24abf2cc5e011ad5a        refs/heads/nixos-20.03
^--- take this sha1 and put it in the URL:
     https://github.com/NixOS/nixpkgs/archive/YOUR-SHA1.zip

--- Prefetch it in the nix store to get its checksum. ---
» nix-prefetch-url https://github.com/NixOS/nixpkgs/archive/1a92d0abfcdbafc5c6e2fdc24abf2cc5e011ad5a.zip --name nixpkgs-20.03-2020-07-15
[30.5 MiB DL]
path is '/nix/store/4hmbsfcwh31j3m309a4gq6jj7whhc277-nixpkgs-20.03-2020-07-15'
1pfgb0r7yykw97n8gx0ga6m5nphxicd4b7mc0d5k863bp7q4cnw5
^--- use this sha256 in default.nix
```

Then, update the name, url and sha256 `nixpkgs` import in `default.nix`:

```nix
# ...
let
nixpkgs = import (builtins.fetchTarball {
        name   = "nixpkgs-20.03-2020-07-15";
        url    = "https://github.com/NixOS/nixpkgs/archive/1a92d0abfcdbafc5c6e2fdc24abf2cc5e011ad5a.zip";
        sha256 = "1pfgb0r7yykw97n8gx0ga6m5nphxicd4b7mc0d5k863bp7q4cnw5";
      }) { /* ... */ };
in {}
# ...

```

### Files in nix/

If you need to get a package from Hackage, use `cabal2nix`:

```
$ cabal2nix cabal://ghcjs-dom-0.2.4.0 | tee ghcjs-dom.nix
$ # or for ghcjs
$ cabal2nix --compiler ghcjs cabal://ghcjs-dom-0.2.4.0 | tee ghcjs-dom-ghcjs.nix
```

There is also `work-on-multi.nix` which provides shells for working on
multi-piece Haskell projects. It's from reflex-platform, but freed from its
dependencies on that project and simplified slightly.

### Issues

Every instance of `doJailbreak` is disabling version checking in Cabal. Most of
the time this works fine, but it indicates bugs in the packages' Cabal
version restrictions.

Carnap currently uses a very old ghcjs-dom from 2016, which is largely fine on
web but requires webkitgtk24x-gtk3 which is obsolete and has been removed from
Nix in late 2019. It is thus currently not possible to build Carnap front end
natively pending this update.

A bunch of packages have broken unit tests on ghcjs. All tests on ghcjs are
accordingly disabled (also, for performance reasons).

### Suggested Nix Resources

Tutorial some of the Nix here is loosely based on:
https://github.com/Gabriel439/haskell-nix

`reflex-platform` documentation that inspired our shell setup:
https://github.com/reflex-frp/reflex-platform/blob/develop/docs/project-development.rst

User's guide to the Haskell infrastructure:
https://nixos.org/nixpkgs/manual/#users-guide-to-the-haskell-infrastructure

Source code to the Haskell infrastructure (has good doc comments):
https://github.com/NixOS/nixpkgs/tree/nixos-20.03/pkgs/development/haskell-modules

Basic information about the builder and e.g. how to build manually:
https://nixos.wiki/wiki/Nixpkgs/Create_and_debug_packages

