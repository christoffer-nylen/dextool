# Mutation Testing Quick Start Guide

This guide shows how to run mutation testing on a real C++ project in a few
minutes using **dextool mutate**.

By the end, you will:
- Generate mutants for your code
- Run your test suite against them
- See which tests are weak or missing

Dextool mutate works by analyzing how your project is compiled. For that, it
needs a `compile_commands.json` file, which describes how each source file is
built.

If your build system does not generate this file, you can use
[BEAR](https://github.com/rizsotto/Bear) to capture it automatically.

You can either follow the instruction below for an example or use
[game_tutorial](examples/game_tutorial).

## GoogleTest

[Google Test project](https://github.com/google/googletest) is used as an
example.

Obtain the project you want to analyze:
```sh
git clone https://github.com/google/googletest.git
cd googletest
```

Generate a JSON compilation database for the project:
```sh
mkdir build
pushd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -Dgtest_build_tests=ON -Dgmock_build_tests=ON ..
make
popd
```

Create a configuration file:
```sh
dextool mutate admin --init
```

Open the resulting `.dextool_mutate.toml` config file and change the following fields:
```toml
[workarea]
include = ["googlemock/include/*", "googlemock/src/*", "googletest/include/*", "googletest/src/*"]

[generic]
mutants = ["sdl"]

[analyze]
exclude = ["googletest/test/*", "googlemock/test/*"]

[compiler]
extra_flags = [ "-D_POSIX_PATH_MAX=1024" ]

[compile_commands]
search_paths = ["./build/compile_commands.json"]

[mutant_test]
build_cmd = "./build.sh"
#test_cmd_dir = ["./build/test"]
test_cmd = "./test.sh"
analyze_using_builtin = ["gtest"]
```

Generate a database containing all mutants:
```sh
dextool mutate analyze
```

Create a file `build.sh` that will build the subject under test when invoked:
```sh
#!/bin/bash
set -e
cd build
make -j$(nproc)
```

Create a file `test.sh` that will run the entire test suite when invoked:
```sh
#!/bin/bash
set -e
cd build
ctest --output-on-failure
```

Make the files executable so they can be used by dextool:
```sh
chmod 755 build.sh test.sh
```

Run the mutation testing on the LCR mutants:
```sh
dextool mutate test
```

You should now see output indicating which mutants were killed or survived.

To generate a report:


For more examples [see here](examples).
