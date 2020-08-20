{ pkgs }:
with pkgs;
stdenv.mkDerivation {
  name = "wrapped-qemu";
  # Remove first two arguments from qemu-kwm, namely "-host cpu"
  buildCommand = ''
    mkdir -p $out/bin
    bins=$(find ${qemu_kvm}/bin -type f -not -name 'qemu-kvm')
    for bin in $bins; do
        ${coreutils}/bin/ln -s $bin $out/bin/
    done
    cat > $out/bin/qemu-kvm << EOF
    #!${python}/bin/python
    import sys, os
    args = [sys.argv[0]] + sys.argv[3:]
    os.execv('${qemu_kvm}/bin/qemu-kvm', args)
    EOF
    ${coreutils}/bin/chmod u+x $out/bin/qemu-kvm
  '';
}
