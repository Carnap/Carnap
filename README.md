# Carnap

Carnap is a free and open-source Haskell framework for creating and exploring
formal languages, logics, and semantics. It lets you quickly and
straightforwardly define languages, construct logics for those languages, and
stipulate their semantics. Carnap then uses your specifications to figure out
how to check proofs in a variety of formal systems using your logic, how to
find the meanings of compound expressions, and a whole lot more.

Carnap's primary application at the moment is powering
[Carnap.io](https://carnap.io), a website supporting online logic instruction
and learning. If  you'd like to seem some demos and more general information,
head over to [Carnap.io/about](https://carnap.io/about). If you'd like to learn
more about using the server as an instructor, head over to the documentation
collection at
[Carnap.io/shared/Documentation](https://carnap.io/shared/Documentation)

If you're interested in contributing to software development or modifying the
software, read on. This README wll help you set up a development environment
for building the server-side and client-side components used on carnap.io.

## Development

### General information

The current development environment is based on [Nix](https://nixOS.org). For
general background on Nix, take a look at
[nixos.org/learn.html](https://nixos.org/learn.html) or [nix.dev](https://nix.dev).

Nix is used to speed up builds and avoid having to compile dependencies,
instead using cached built versions from nixpkgs. It also makes it easy to
[Dockerize](https://nixos.org/nixpkgs/manual/#sec-pkgs-dockerTools) (see also
NixOps) and implement CI.

Carnap has a GHCJS (client side) and a GHC (server side) part.

Building Carnap-Server depends on the client side components being available at
`client-out` or otherwise linked into its static folder. This will be handled
automatically by the approaches to building the client listed below, but the
client needs to be built before the server.

Nix does not support incremental package builds, so the suggested development
workflow is to use `cabal` in a shell. A `Makefile` has been provided to make
this easier.

### Nix setup

Install Nix with your *non-root* user account:

```
$ bash <(curl -L https://nixos.org/nix/install)
```

macOS 10.15 (Catalina) users may need to follow additional steps, documented at
[nixos.org/nix/manual/#sect-macos-installation](https://nixos.org/nix/manual/#sect-macos-installation).

You can significantly speed up builds by using binaries for Carnap dependencies
from @lf-'s [Cachix](https://cachix.org/) instance. To use it:

```
$ # Install Cachix:
$ nix-env -iA cachix -f https://cachix.org/api/v1/install
$ # Use the Carnap Cachix
$ cachix use carnap
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

You should then be able to access your development server at
`http://localhost:3000`

To perform the process manually, first make sure to copy
`Carnap-Server/config/settings-example.yml` to
`Carnap-Server/config/settings.yml`, and to create a data directory (in the
below, called `dataroot`). Then run:

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

## Deployment

### Docker

There is experimental Docker support for Carnap. Currently, diagrams support is
broken, which impacts some chapters of the Carnap textbook.

Images are available via the GitHub container registry at
`docker.pkg.github.com/carnap/carnap/carnap:latest`.

Note that Carnap docker images are about 3GB uncompressed and about 500MB to
download.

If you'd like to build an image locally for development/testing, run:

```
nix-build release.nix -A docker -o docker-out
```

then load it into the docker daemon with:

```
docker image load -i docker-out
```

It will be available under the image name `carnap:latest`.

To run Carnap under docker:

```
docker run --rm -v carnap_data:/data -e APPROOT=http://your-app-root.com
```

For production deployment, set the environment variable SQLITE=false and supply
`PGUSER`, `PGPASS`, `PGHOST`, and if required, `PGPORT` and `PGDATABASE` for
your postgresql database instance.

The docker building setup does not require KVM support in the host kernel, and
if you wish to build your images on a machine without it, run nix-build with
the added argument `--arg hasKvm false`.

## Maintainer information

### CI requirements

CI requires that a Cachix signing key for the Cachix cache be supplied in the
`CACHIX_SIGNING_KEY` Secret in the GitHub repository settings for artifacts to
be pushed to Cachix.

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

Carnap currently uses an older ghcjs-dom from 2016, which is largely fine on
web but requires webkitgtk24x-gtk3, which was been removed from Nix in late
2019. It is thus currently not possible to build the Carnap front end natively
(i.e. for embedding in non-browser applications) pending this update.

A bunch of packages have broken unit tests on ghcjs. All tests on ghcjs are
accordingly disabled (also, for performance reasons).

### Suggested Nix Resources

Blog post on Carnap's nix implementation: https://lfcode.ca/blog/nix-and-haskell

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
