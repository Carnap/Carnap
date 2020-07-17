.PHONY: shell-ghc build-ghc build-ghc tags
TARGET := all

help:
	@echo "Supported actions: run, shell-ghc, build-ghc, shell-ghcjs, build-ghcjs, tags"

run:
	cd Carnap-Server; APPROOT="http://localhost:3000" DATAROOT="../dataroot" \
		BOOKROOT="../Carnap-Book/" \
		cabal run -f dev Carnap-Server

shell-ghc:
	nix-shell -A ghcShell

build-ghc:
	cabal new-build -f dev $(TARGET)

shell-ghcjs:
	nix-shell -A ghcjsShell

build-ghcjs:
	cabal --project-file=cabal-ghcjs.project --builddir=dist-ghcjs new-build $(TARGET)
	# make a fake nix output directory so we don't have to change the symlinks from a nix-built
	# client (allowing people working only on the server to download a client from nix cache)
	mkdir -p .cabal-fake-client-out/bin
	ln -rsf dist-ghcjs/build/*/ghcjs-*/Carnap-GHCJS-*/x/AllActions/build/AllActions/AllActions.jsexe .cabal-fake-client-out/bin/
	ln -sfn .cabal-fake-client-out client-out

tags:
	hasktags -R .
