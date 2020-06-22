SHELL := bash
.ONESHELL:
.SHELLFLAGS := -eu -o pipefail -c
.DELETE_ON_ERROR:
MAKEFLAGS += --warn-undefined-variables
MAKEFLAGS += --no-builtin-rules

ifeq ($(origin .RECIPEPREFIX), undefined)
  $(error This Make does not support .RECIPEPREFIX. Please use GNU Make 4.0 or later)
endif
.RECIPEPREFIX = >

.PHONY: clean build-client build-server build-server-dev run-server link-js

PROJECT_NAME := Carnap-Server

# workaround for https://github.com/commercialhaskell/stack/issues/793
STACK := LC_ALL=C.utf-8 stack

JSEXE = $(wildcard dist-newstyle/build/*/*/Carnap-GHCJS-*/x/AllActions/build/AllActions/AllActions.jsexe)
JS_LINKS_DIR := Carnap-Server/static/ghcjs/allactions
jsexe_path = $(shell realpath --relative-to ${JS_LINKS_DIR} ${JSEXE})
link_jsexe = ln -sf ${jsexe_path}/$(1) ${JS_LINKS_DIR}

all: build-server-dev

# XXX: slightly evil workaround for ridiculous paths from Cabal such as
# ./dist-newstyle/build/x86_64-linux/ghcjs-8.6.0.1/Carnap-GHCJS-0.1.0.0/x/AllActions/build/AllActions/AllActions.jsexe
# that we should not generate. I give up. Just track completion ourselves.
client-build.done:
> cabal update
> cabal new-build all
> touch client-build.done
> $(MAKE) link-js

build-client: client-build.done

build-server: build-client
> ${STACK} build

build-server-dev: build-client
> ${STACK} build --flag Carnap-Server:dev

clean:
> ${STACK} clean --full
> cabal new-clean
> rm -rf './${JS_LINKS_DIR}/'*
> rm client-build.done

Carnap-Server/static/ghcjs/allactions/%:
> $(call link_jsexe,$*)

link-js: Carnap-Server/static/ghcjs/allactions/runmain.js \
		 Carnap-Server/static/ghcjs/allactions/out.js \
		 Carnap-Server/static/ghcjs/allactions/lib.js

run-server:
> mkdir -p Carnap-Book/cache
> mkdir -p dataroot
> cd Carnap-Server
> APPROOT="http://localhost:3000" DATAROOT="../dataroot" BOOKROOT="../Carnap-Book/" ${STACK} exec Carnap-Server

tags:
> hasktags -R .
