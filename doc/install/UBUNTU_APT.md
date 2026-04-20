# Ubuntu APT Packaging

This document describes the maintainer workflow for building the Debian package
in this repository and publishing Ubuntu builds through a Launchpad PPA.

The packaged plugin set in v1 is:
 - `dextool`
 - `dextool-ctestdouble`
 - `dextool-cpptestdouble`
 - `dextool-mutate`

The `analyze`, `uml`, and `example` plugins are kept in the source tree, but
they are not part of the default packaged build.

## Maintainer prerequisites

Install the packaging and build tools on an Ubuntu machine:

```sh
sudo apt update
sudo apt install build-essential debhelper devscripts dput lintian cmake clang llvm-dev libclang-dev libsqlite3-dev ldc
```

## Local release build

Build the release binaries with the `ldmd2` frontend from the `ldc` toolchain
before preparing a package upload:

```sh
cmake -S . -B build-release \
    -DD_COMPILER=ldmd2 \
    -DCMAKE_BUILD_TYPE=Release \
    -DLOW_MEM=ON \
    -DDEXTOOL_USE_MOLD=OFF
cmake --build build-release -j1
```

Smoke-test the built binaries:

```sh
./build-release/dextool --plugin-list
./build-release/dextool ctestdouble --help
./build-release/dextool cpptestdouble --help
./build-release/dextool mutate report --help
```

If you want to run mutate validation targets during development, configure a
test build and run the targets sequentially against the same build directory:

```sh
cmake -S . -B build-test \
    -DD_COMPILER=ldmd2 \
    -DCMAKE_BUILD_TYPE=Release \
    -DBUILD_TEST=ON \
    -DLOW_MEM=ON \
    -DDEXTOOL_USE_MOLD=OFF
cmake --build build-test --target mutate_unittest__run --target dextool_debug-mutate_integration__run --parallel 1
```

## Build the Debian package

Create a local binary package:

```sh
debuild -us -uc -b
lintian ../dextool_*_amd64.changes
```

Install the package locally and verify the installed commands:

```sh
sudo apt install ../dextool_*_amd64.deb
dextool --plugin-list
dextool ctestdouble --help
dextool cpptestdouble --help
dextool mutate report --help
```

## Build and upload a Launchpad source package

The Debian packaging in this repo is Debian-compatible by default. Before each
PPA upload, update `debian/changelog` for the target Ubuntu series and add a
PPA-specific suffix such as `~ppa1`.

Example for `jammy`:

```sh
dch --distribution jammy --local "~ppa1" "Launchpad PPA build for jammy"
debuild -S -sa
lintian ../dextool_*_source.changes
dput ppa:<launchpad-team>/<ppa-name> ../dextool_*_source.changes
```

Repeat the same process for `noble`, updating the changelog distribution before
building the source package for that series.

Once the PPA has published binaries, users install the package with:

```sh
sudo add-apt-repository ppa:<launchpad-team>/<ppa-name>
sudo apt update
sudo apt install dextool
```
