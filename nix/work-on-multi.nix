# Collect the dependencies of multiple packages and produce a shell environment
# for working on all of those packages

# This file is a part of reflex-platform
# (https://github.com/reflex-frp/reflex-platform), modified for use in Carnap

# Copyright (c) 2014, Ryan Trinkle
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# * Neither the name of the {organization} nor the names of its
#   contributors may be used to endorse or promote products derived from
#   this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

{ nixpkgs, generalDevTools }:
let
  inherit (nixpkgs.haskell.lib) overrideCabal;
  inherit (nixpkgs) lib;
in

{ env, envPackages, shellToolOverrides ? _: _: {} }:

let
  inherit (builtins) listToAttrs filter attrValues all concatLists;
    combinableAttrs = p: [
      "buildDepends"
      "buildTools"
      "executableFrameworkDepends"
      "executableHaskellDepends"
      "executablePkgconfigDepends"
      "executableSystemDepends"
      "executableToolDepends"
      "extraLibraries"
      "libraryFrameworkDepends"
      "libraryHaskellDepends"
      "libraryPkgconfigDepends"
      "librarySystemDepends"
      "libraryToolDepends"
      "pkgconfigDepends"
      "setupHaskellDepends"
    ] ++ lib.optionals (p.doCheck or true) [
      "testDepends"
      "testFrameworkDepends"
      "testHaskellDepends"
      "testPkgconfigDepends"
      "testSystemDepends"
      "testToolDepends"
    ] ++ lib.optionals (p.doBenchmark or false) [
      "benchmarkDepends"
      "benchmarkFrameworkDepends"
      "benchmarkHaskellDepends"
      "benchmarkPkgconfigDepends"
      "benchmarkSystemDepends"
      "benchmarkToolDepends"
    ];

    concatCombinableAttrs = haskellConfigs: lib.filterAttrs
      (n: v: v != [])
      (lib.zipAttrsWith (_: concatLists) (map
        (haskellConfig: lib.listToAttrs (map
          (name: {
            inherit name;
            value = haskellConfig.${name} or [];
          })
          (combinableAttrs haskellConfig)))
        haskellConfigs
        ));

    # grabs, effectively, the set from the cabal2nix'd file
    getHaskellConfig = p: (overrideCabal p (args: {
      passthru = (args.passthru or {}) // {
        out = args;
      };
    })).out;

    notInTargetPackageSet = p: all (pname: (p.pname or "") != pname) envPackages;
    baseTools = generalDevTools {};
    overriddenTools = baseTools // shellToolOverrides env baseTools;
    depAttrs = lib.mapAttrs (_: v: filter notInTargetPackageSet v) (concatCombinableAttrs (concatLists [
      # call getHaskellConfig on [env.${name} for name in envPackages] list
      (map getHaskellConfig (lib.attrVals envPackages env))
      [{
        buildTools = [
          (nixpkgs.buildEnv {
            name = "build-tools-wrapper";
            paths = attrValues overriddenTools;
            pathsToLink = [ "/bin" ];
            extraOutputsToInstall = [ "bin" ];
          })
          overriddenTools.Cabal
        ];
      }]
    ]));

in (env.mkDerivation (depAttrs // {
  pname = "work-on-multi--combined-pkg";
  version = "0";
  license = null;
})).env
