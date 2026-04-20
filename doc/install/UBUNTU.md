# Install Dextool on Ubuntu

This document covers building dextool from source on Ubuntu. For the Debian and
Launchpad PPA packaging workflow, see [UBUNTU_APT.md](UBUNTU_APT.md).

## Install the build dependencies

```sh
sudo apt update
sudo apt install build-essential cmake clang llvm-dev libclang-dev libsqlite3-dev ldc
```

If your Ubuntu release only exposes versioned LLVM packages, install the
matching `clang-X`, `llvm-X-dev`, and `libclang-X-dev` packages instead.

The supported compiler versions are tracked in:
 - [dmd minimal version](../../Docker/partial/dmd_min_version)
 - [dmd max version](../../Docker/partial/dmd_latest_version)
 - [ldc minimal version](../../Docker/partial/ldc_min_version)
 - [ldc max version](../../Docker/partial/ldc_latest_version)

## Build and install

```sh
git clone https://github.com/joakim-brannstrom/dextool.git
cd dextool
cmake -S . -B build \
    -DD_COMPILER=ldmd2 \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_INSTALL_PREFIX="$HOME/local"
cmake --build build
cmake --install build
```

The default build installs:
 - `dextool`
 - `dextool-ctestdouble`
 - `dextool-cpptestdouble`
 - `dextool-mutate`
