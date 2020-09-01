.PHONY: help shell-ghc build-ghc shell-ghcjs build-ghcjs tags
TARGET := all

help:
	@echo "Supported actions: run, shell-ghc, build-ghc, shell-ghcjs, build-ghcjs, tags"

run:
	cd Carnap-Server && \
	cp -n config/settings-example.yml config/settings.yml && \
	mkdir -p ../dataroot && \
	mkdir -p ../Carnap-Book/cache && \
	APPROOT="http://localhost:3000" DATAROOT="../dataroot" \
		BOOKROOT="../Carnap-Book/" \
		cabal run -f dev Carnap-Server

shell-ghc:
	nix-shell

build-ghc:
ifeq ($(origin NIX_STORE),undefined)
	$(error It seems like this is not being run in a nix shell. Try `make shell-ghc` first)
endif
	cabal new-build -f dev $(TARGET)

shell-ghcjs:
	nix-shell --arg ghcjs true

# I don't think I can easily enter a shell for the user if they forget unfortunately :(
build-ghcjs:
ifeq ($(origin NIX_STORE),undefined)
	$(error It seems like this is not being run in a nix shell. Try `make shell-ghcjs` first)
endif
	cabal --project-file=cabal-ghcjs.project --builddir=dist-ghcjs new-build $(TARGET)
	# make a fake nix output directory so we don't have to change the symlinks from a nix-built
	# client (allowing people working only on the server to download a client from nix cache)
	mkdir -p .cabal-fake-client-out/bin
	ln -rsf dist-ghcjs/build/*/ghcjs-*/Carnap-GHCJS-*/x/AllActions/build/AllActions/AllActions.jsexe .cabal-fake-client-out/bin/
	ln -sfn .cabal-fake-client-out client-out

tags:
	hasktags -R .
