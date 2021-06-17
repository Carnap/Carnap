.PHONY: help shell-ghc build-ghc shell-ghcjs build-ghcjs tags build-production
TARGET := all

help:
	@echo "Usage: make [options] [target]"
	@echo ""
	@echo "Supported targets:"
	@echo "    build-production 	Build and bundle everything needed to run the server in production"
	@echo "    build-docker 		Build a production docker container"
	@echo "    build-ghcjs 	 		Build a development client JavaScript with GHCJS"
	@echo "    build-ghc 			Build a development server with GHC"
	@echo "    shell-ghcjs		    Enter a nix shell for GHCJS client development"
	@echo "    shell-ghc		    Enter a nix shell for GHC server development"
	@echo "    run				    Run the server locally, with data saved in this directory"
	@echo "    tags				    Generate source code tags for development"
	@echo ""
	@echo "For more usage instructions, see README."


build-production:
	@echo "building client..."
	nix-build -j4 -A client -o client-out
	@echo "building server..."
	nix-build -j4 -A server -o server-out
	@echo "creating bundle directory..."
	mkdir bundle
	@echo "copying files..."
	cp -r server-out/share/* bundle
	cp server-out/bin/Carnap-Server bundle
	chmod -R +w bundle
	@echo "compressing..."
	tar -hczf carnap.tar.gz bundle
	@echo "cleaning up..."
	rm -r bundle

build-docker:
	nix-build release.nix -A docker -o docker-out

run:
ifeq ($(origin NIX_STORE),undefined)
	nix-shell --run 'make run'
else
	cd Carnap-Server && \
	cp -n config/settings-example.yml config/settings.yml && \
	mkdir -p ../dataroot && \
	mkdir -p ../Carnap-Book/cache && \
	APPROOT="http://localhost:3000" DATAROOT="../dataroot" \
		BOOKROOT="../Carnap-Book/" \
		cabal run -f dev Carnap-Server
endif

shell-ghc:
	nix-shell

build-ghc:
ifeq ($(origin NIX_STORE),undefined)
	nix-shell --run 'make build-ghc'
else
	cp -n Carnap-Server/config/settings-example.yml Carnap-Server/config/settings.yml && \
	cabal new-build -f dev $(TARGET)
endif

shell-ghcjs:
	nix-shell --arg ghcjs true

# I don't think I can easily enter a shell for the user if they forget unfortunately :(
build-ghcjs:
ifeq ($(origin NIX_STORE),undefined)
	nix-shell --run 'make build-ghcjs'
else
	cabal --project-file=cabal-ghcjs.project --builddir=dist-ghcjs new-build $(TARGET)
	# make a fake nix output directory so we don't have to change the symlinks from a nix-built
	# client (allowing people working only on the server to download a client from nix cache)
	mkdir -p .cabal-fake-client-out/bin
	ln -rsf dist-ghcjs/build/*/ghcjs-*/Carnap-GHCJS-*/x/AllActions/build/AllActions/AllActions.jsexe .cabal-fake-client-out/bin/
	ln -sfn .cabal-fake-client-out client-out
endif

tags:
	hasktags -R .
