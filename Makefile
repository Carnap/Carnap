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

tags:
	hasktags -R .
