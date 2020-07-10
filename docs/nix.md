## Implemented Carnap build process

Nix is used to speed up builds and avoid having to compile dependencies,
instead using cached built versions from nixpkgs. It also makes it easy to
[Dockerize](https://nixos.org/nixpkgs/manual/#sec-pkgs-dockerTools) (see also
NixOps) and implement CI.

Fundamentally, Carnap has two sides that need to be built: client side and
server side. Client side has a dep tree of `Carnap` <- `Carnap-Client` <-
`Carnap-GHCJS`. Server side is `Carnap` <- `Carnap-Client` <- `Carnap-Server`.

`Carnap-Server` also depends on an evil link/copy of the `Carnap-GHCJS`
`AllActions` JS executable into its static folder.

### Sins

Every instance of `doJailbreak` is disabling version checking in Cabal. Most of
the time this works fine, but it indicates bugs in the packages' Cabal
version restrictions.

A bunch of packages have broken unit tests on ghcjs. Their tests are
accordingly disabled.

## Development

### Build Carnap-Server

```
$ nix-build -j4 -A server
```

This will also automatically build the client and make the appropriate symbolic links.

### Build Carnap-GHCJS

(note: takes about 9-10GB of RAM at the final linking stage)

```
$ nix-build -j4 -A client
```

### Get a development shell

```
# you can omit --pure at risk of accidentally using system tools
$ nix-shell --pure
```

### Generate the `.nix` files in each subproject

For example:

```
$ cd Carnap-Client; cabal2nix . > Carnap-Client.nix
```

## Nix Documentation

Tutorial some of the Nix here is loosely based on: https://github.com/Gabriel439/haskell-nix

User's guide to the Haskell infrastructure: https://nixos.org/nixpkgs/manual/#users-guide-to-the-haskell-infrastructure

Source code to the Haskell infrastructure (has good doc comments): https://github.com/NixOS/nixpkgs/tree/nixos-20.03/pkgs/development/haskell-modules

Basic concepts around the builder: https://nixos.wiki/wiki/Nixpkgs/Create_and_debug_packages
