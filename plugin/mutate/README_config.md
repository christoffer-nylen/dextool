# Configuration

This document is a reference for the current `dextool mutate` commands, flags,
and `.dextool_mutate.toml` configuration keys.

It is intended to stay aligned with:

- `dextool mutate <command> --help`
- `dextool mutate admin --dump-config`
- the current argument/config parser in `source/dextool/plugin/mutate/frontend/argparser.d`

For a step-by-step introduction, see [the quick start guide](README_tutorial.md).

- [Command Line Options](#command-line-options)
  - [Shared flags](#shared-flags)
  - [Admin](#admin)
  - [Analyze](#cmd-analyze)
  - [Generate](#generate)
  - [Report](#cmd-report)
  - [Test](#test)
- [Configuration File](#configuration-file)
  - [General notes](#config-notes)
  - [\[workarea\]](#workarea)
  - [\[generic\]](#generic)
  - [\[analyze\]](#config-analyze)
  - [\[schema\]](#schema)
  - [\[coverage\]](#coverage)
  - [\[database\]](#database)
  - [\[compiler\]](#compiler)
  - [\[compile_commands\]](#compile_commands)
  - [\[mutant_test\]](#mutant_test)
  - [\[report\]](#config-report)
  - [\[test_group\]](#test_group)
  - [\[test\]](#config-test)
  - [Deprecated compatibility keys](#deprecated-compatibility-keys)
- [Resources](#resources)

# Command Line Options

The sections below describe the flags exposed by the mutate plugin today.
Unless noted otherwise, paths and glob patterns are interpreted relative to
`--out` / `[workarea].root`.

## Shared flags

- `-c`, `--config`: Load a user configuration file. The default is
  `.dextool_mutate.toml`.

  Dextool loads system configuration first and then overlays the user
  configuration from `--config`, so the user file can override any system
  setting.

  System configuration is searched for in this order:

  - `$XDG_CONFIG_HOME/dextool/dextool_mutate.toml`
  - `dirname(<dextool executable>)/config/dextool_mutate.toml`
  - `dirname(dirname(<dextool executable>))/config/dextool_mutate.toml`
  - each entry in `$XDG_CONFIG_DIRS` as
    `<dir>/dextool/config/dextool_mutate.toml`

- `--db`: Path to the sqlite3 database to use. The default is
  `dextool_mutate.sqlite3`.

- `--out`: Root path used for mutation and reporting. The default is `.`.

- `-h`, `--help`: Print help for the current mutate subcommand.

- `--include`, `--exclude`: Restrict which files are eligible for mutation.
  These flags are available on `analyze`, `generate`, `report`, and `test`.
  Files must match at least one include pattern and none of the exclude
  patterns. The default is `["*"]` for include and an empty exclude list.

- `--compile-db`: Override the compilation database to read compile flags from.
  This flag is available on `analyze` and `report`.

- `--diff-from-stdin`: Read a unified git diff from stdin and restrict work to
  the changed files or lines. This flag is available on `analyze`, `report`,
  and `test`.

  Example:

  ```sh
  git diff | dextool mutate analyze --diff-from-stdin
  git diff | dextool mutate test --diff-from-stdin
  git diff | dextool mutate report --diff-from-stdin
  ```

- `--profile`: Print internal performance/profiling information. This flag is
  available on `analyze` and `report`.

## Admin

Administrative operations for bootstrapping and maintaining the mutation
database.

- `--init`: Write a starter `.dextool_mutate.toml` into the current workspace.

- `--dump-config`: Print the resolved TOML configuration that dextool is using.

- `-m`, `--mutant`: Select mutation kinds for admin operations that act on
  mutation kinds. Accepted values are `all`, `ror`, `rorp`, `lcr`, `aor`,
  `uoi`, `sdl`, `dcr`, `lcrb`, `aors`, and `cr`.

- `--mutant-sub-kind`: Select one or more specific sub-kinds for operations
  such as `resetMutantSubKind`. The full set of values mirrors the internal
  `Mutation.Kind` enum and is printed by `dextool mutate admin --help`.

- `--operation`: Administrative operation to perform. Accepted values are:
  `none`, `resetMutant`, `removeMutant`, `removeTestCase`, `markMutant`,
  `removeMarkedMutant`, `resetTestCase`, `compact`, `stopTimeoutTest`,
  `resetMutantSubKind`, and `clearWorklist`.

- `--test-case-regex`: Regex used by operations that remove or reset test
  cases.

- `--status`: Filter mutants by their current status. Accepted values are
  `unknown`, `killed`, `alive`, `killedByCompiler`, `timeout`, `noCoverage`,
  `equivalent`, `skipped`, and `memOverload`.

- `--to-status`: Target status to write when an admin operation resets or marks
  mutants. It accepts the same values as `--status`.

- `--id`: Mutant id to operate on.

- `--rationale`: Free-form explanation stored when marking a mutant manually.

## Analyze <a id="cmd-analyze"></a>

Analyze the project and save mutation points to the database.

- `--allow-errors`: Allow compilation errors during analysis. This is useful
  when clang can still extract useful information even though some translation
  units do not parse cleanly.

- `--compile-db`: Use a specific `compile_commands.json` instead of the paths
  from config.

- `--diff-from-stdin`: Only analyze and save mutants that fall within files
  changed by the diff on stdin.

- `--fast-db-store`: Disable sqlite safety features to speed up database
  writes. This can be much faster, but an interrupted write can corrupt the
  database.

- `--file-include`, `--file-exclude`: Restrict which entries from the
  compilation database are analyzed. These filters are separate from
  `--include` / `--exclude`, which control what is eligible for mutation.

- `--force-save`: Save all analyzed files even if dextool believes they are
  unchanged.

- `--id-algorithm`: Control how mutant ids are generated. Accepted values are
  `relaxed` and `strict`.

  `strict` ties ids to the full file contents.
  `relaxed` ties ids to the surrounding scope, which reduces unnecessary
  re-testing when unrelated parts of a file move.

- `--in`: Analyze a specific input file instead of reading all entries from the
  compilation database.

- `-m`, `--mutant`: Select which mutation kinds to discover and save. Accepted
  values are `all`, `ror`, `rorp`, `lcr`, `aor`, `uoi`, `sdl`, `dcr`, `lcrb`,
  `aors`, and `cr`.

- `--no-prune`: Do not remove database entries for files that were not seen in
  the current analyze run.

- `--profile`: Print analyzer performance data.

- `--schema-min-mutants`: Minimum number of mutants required before a schema is
  saved.

- `--schema-mutants`: Soft upper limit for how many mutants to place in one
  schema.

- `--system-compiler`: Derive system include paths from this compiler instead
  of the compiler recorded in the compilation database.

- `--threads`: Number of worker threads to use for analysis.

## Generate

Generate a concrete mutated source file for one mutant.

- `--id`: Required. The mutant id to materialize into source code.

- `-m`, `--mutant`: Filter by mutation kind. Accepted values are `all`, `ror`,
  `rorp`, `lcr`, `aor`, `uoi`, `sdl`, `dcr`, `lcrb`, `aors`, and `cr`.

- Shared flags such as `--config`, `--db`, `--out`, `--include`, and
  `--exclude` also apply.

## Report <a id="cmd-report"></a>

Generate reports from the current mutation database.

- `--compile-db`: Override the compilation database used when report generation
  needs compile-db-aware file information.

- `--diff-from-stdin`: Restrict diff-aware report output to the changed lines
  from stdin.

- `--high-interest-mutants-nr`: Number of mutants to show in the high-interest
  section.

- `--logdir`: Output directory for generated report files. The default is `.`.

- `-m`, `--mutant`: Deprecated for `report`. It is still accepted for backward
  compatibility, but it no longer drives report generation.

- `--profile`: Print report profiling information.

- `--section`: Select report sections. Accepted values are `alive`, `killed`,
  `all_mut`, `summary`, `mut_stat`, `tc_killed`, `tc_stat`, `tc_map`,
  `tc_suggestion`, `tc_killed_no_mutants`, `tc_full_overlap`,
  `tc_full_overlap_with_mutation_id`, `tc_groups`, `tc_min_set`,
  `tc_similarity`, `tc_groups_similarity`, `mut_recommend_kill`, `diff`,
  `tc_unique`, `marked_mutants`, and `trend`.

- `--section-tc_stat-num`: Number of test cases to include in the `tc_stat`
  report section.

- `--section-tc_stat-sort`: Sort order for `tc_stat`. Accepted values are
  `top` and `bottom`.

- `--style`: Report format. Accepted values are `plain`, `compiler`, `json`,
  and `html`.

- `--test-metadata`: Path to a JSON file containing per-test metadata used by
  some report views.

Section support varies by report style. `plain` is the baseline and `compiler`
follows the same content model but emits compiler-like diagnostics.

| Section                          | plain | json | html |
|----------------------------------|-------|------|------|
| alive                            | x     | x    |      |
| all_mut                          | x     | x    | (x)  |
| diff                             |       | x    | x    |
| killed                           | x     | x    |      |
| marked_mutants                   | x     |      |      |
| mut_recommend_kill               |       |      | (x)  |
| mut_stat                         | x     |      |      |
| summary                          | x     | x    | x    |
| tc_full_overlap                  | x     |      | (x)  |
| tc_full_overlap_with_mutation_id | x     |      | x    |
| tc_groups                        |       |      | x    |
| tc_groups_similarity             |       |      | x    |
| tc_killed                        | x     |      |      |
| tc_killed_no_mutants             | x     | x    | (x)  |
| tc_map                           | x     |      |      |
| tc_min_set                       |       |      | x    |
| tc_similarity                    |       |      | x    |
| tc_stat                          | x     | x    |      |
| tc_suggestion                    |       |      | x    |
| tc_unique                        |       | x    | (x)  |
| trend                            | x     | x    | x    |

`(x)` means the style may emit the information implicitly or via a style-
specific page even if the section is not a one-to-one toggle in that output
format.

## Test

Execute mutation testing against the previously analyzed mutants.

- `-L`: Restrict testing to specific files and line ranges. The format is
  `<file>:<start>-<end>`.

  Example:

  ```sh
  dextool mutate test -L src/foo.cpp:10-20
  ```

- `--build-cmd`: Command used to build the project and test binaries.

- `--cont-test-suite`: Enable the periodic sanity check that re-runs the test
  suite with no mutant injected.

- `--cont-test-suite-period`: How often the periodic sanity check runs, in
  number of tested mutants.

- `--diff-from-stdin`: Restrict testing to mutants that fall within the diff on
  stdin.

- `--dry-run`: Exercise the control flow without writing mutants to the source
  tree. Mainly useful for tests and experimentation.

- `--load-behavior`: Behavior when the load threshold is exceeded. Accepted
  values are `nothing`, `slowdown`, and `halt`.

- `--load-threshold`: 15-minute load average threshold used by
  `--load-behavior`. The default is the number of virtual cores plus three.

- `--log-coverage`: Save the generated coverage-instrumented files for later
  inspection.

- `--max-alive`: Stop after this many alive mutants have been found. This is
  only effective together with `-L` or `--diff-from-stdin`.

- `--max-runtime`: Stop the current test run after the given duration. Supported
  units are `weeks`, `days`, `hours`, `minutes`, `seconds`, and `msecs`.

  Example:

  ```sh
  dextool mutate test --max-runtime "1 hours 30 minutes"
  ```

- `--metadata`: Path to a JSON file used to increase testing priority for
  mutants in specific files. The file format is currently:

  ```json
  {
    "file-prio": ["src/foo.cpp", "src/bar.cpp"]
  }
  ```

- `-m`, `--mutant`: Deprecated for `test`. It is still accepted for backward
  compatibility, but the active mutation set comes from analysis/config.

- `--no-skipped`: Disable the skip heuristic that can mark some covered mutants
  as `skipped` without executing them individually.

- `--order`: Choose the mutant execution order. Accepted values are `random`,
  `consecutive`, and `bySize`. `bySize` is the current default.

- `--schema-check`: Sanity-check a schema by running the test suite once with
  the schema injected and no mutant activated.

- `--schema-log`: Save generated schema source for later inspection.

- `--schema-min-mutants`: Minimum number of alive mutants a schema must contain
  before it is used in the test phase.

- `--schema-only`: Stop after the schema-backed portion of testing completes.

- `--schema-parallel-mutants`: Number of mutants to test in parallel inside one
  schema execution.

- `--schema-train`: Only compile schemas and run the training path for the
  adaptive schema generator.

- `--schema-use`: Enable schemata in the test phase.

- `--test-case-analyze-builtin`: Built-in parser for test output. Accepted
  values are `gtest`, `ctest`, `makefile`, and `test_cmd`.

- `--test-case-analyze-cmd`: External command used to parse test output and
  identify failing test cases.

- `--test-cmd`: Command used to run the test suite.

- `--test-cmd-checksum`: Compare test binary checksums before and after
  mutation and only run binaries that changed.

- `--test-timeout`: Fixed timeout for the test suite, in milliseconds. Setting
  this disables the adaptive timeout derivation used by default.

- `--timeout-scale`: Multiplier used when computing schema-related timeouts.

- `--use-early-stop`: Stop executing test commands for a mutant as soon as one
  test command fails.

# Configuration File

The template written by:

```sh
dextool mutate admin --init
```

is the best starting point for a new project. The sections below describe every
currently parsed TOML key.

## General notes <a id="config-notes"></a>

- Not every CLI flag has a TOML equivalent. Run-scoped flags such as `-L`,
  `--diff-from-stdin`, `--profile`, `--log-coverage`, `--max-alive`,
  `--max-runtime`, `--load-behavior`, `--load-threshold`, `--metadata`,
  `--schema-log`, `--schema-only`, and `--no-skipped` are CLI-only today.

- Many CLI names map cleanly to TOML keys, but not always with the same text.
  For example, `--test-case-analyze-cmd` maps to `[mutant_test].analyze_cmd`,
  `--test-timeout` maps to `[mutant_test].test_cmd_timeout`, and
  `--timeout-scale` maps to `[schema].timeout_scale`.

## [workarea]

Controls the part of the source tree that mutate is allowed to change and
report on.

- `root`: Root directory for analyze, test, and report.

- `include`: Glob patterns, relative to `root`, that are eligible for mutation.

- `exclude`: Glob patterns, relative to `root`, that are removed from the
  mutation set even if they match `include`.

## [generic]

Options shared across phases.

- `mutants`: Default mutation kinds to use when no CLI mutation list is given.
  Accepted values are `all`, `ror`, `rorp`, `lcr`, `aor`, `uoi`, `sdl`, `dcr`,
  `lcrb`, `aors`, and `cr`.

## [analyze] <a id="config-analyze"></a>

Options that affect the analyze phase.

- `include`: Glob patterns that select which compile-db entries are analyzed.

- `exclude`: Glob patterns that remove compile-db entries from analysis.

- `threads`: Number of analysis worker threads.

- `prune`: If `true`, remove files and orphaned mutants that are no longer seen
  during analysis.

- `test_paths`: Files or directories that should be checksummed/timestamped so
  mutate can tell when test inputs changed.

- `test_include`: Glob patterns used when traversing `test_paths`.

- `test_exclude`: Glob patterns excluded while traversing `test_paths`.

- `id_algo`: Mutant id generation algorithm. Accepted values are `relaxed` and
  `strict`.

## [schema]

Controls schema generation and schema-backed mutation testing.

- `use`: Enable schemata.

- `runtime`: How the schema runtime is provided. Accepted values are `inject`
  and `library`.

- `inject_runtime_impl`: Optional array of `[path, language]` pairs limiting
  runtime injection to specific files. `language` is typically `c` or `cpp`.

- `parallel_mutants`: Number of mutants to test in parallel inside one schema.

- `min_mutants_per_schema`: Minimum number of mutants required before a schema
  is stored or used.

- `mutants_per_schema`: Soft upper limit for how many mutants a schema should
  contain. `0` means no limit.

- `check_schemata`: If `true`, run a sanity-check test pass after schema
  injection.

- `timeout_scale`: Multiplier used when computing schema-related timeouts.

## [coverage]

Controls optional coverage-guided pruning.

- `use`: Enable coverage-guided pruning.

- `runtime`: How the coverage runtime is provided. Accepted values are
  `inject` and `library`.

- `inject_runtime_impl`: Optional array of `[path, language]` pairs limiting
  runtime injection to specific files.

## [database]

Database location.

- `db`: Path to the sqlite database file.

## [compiler]

Compiler-related adjustments made during analysis and generated code handling.

- `flags`: Extra compiler flags typically supplied from system configuration.

- `extra_flags`: Extra compiler flags typically supplied from user/project
  configuration.

- `force_system_includes`: If `true`, pass discovered system include paths with
  `-I` instead of `-isystem`.

- `use_compiler_system_includes`: Compiler executable to derive system includes
  from instead of the compiler recorded in `compile_commands.json`.

- `allow_errors`: Allow compilation errors during analysis.

## [compile_commands]

Controls how dextool finds and filters `compile_commands.json`.

- `search_paths`: Files and/or directories to search for compilation
  databases.

- `filter`: Compile flags that should be removed before clang-based analysis.

- `skip_compiler_args`: Number of leading arguments to skip before the real
  compiler binary appears. Useful for wrappers or launchers.

## [mutant_test]

Options for the test phase.

- `build_cmd`: Command used to build the project and tests.

- `test_cmd_dir`: Directories to scan for executable test binaries. At least
  one of `test_cmd_dir` or `test_cmd` must be configured.

- `test_cmd_dir_search`: How `test_cmd_dir` is scanned. Accepted values are
  `recursive` and `shallow`.

- `test_cmd_dir_flag`: Extra arguments appended to each executable discovered
  via `test_cmd_dir`.

- `test_cmd`: Explicit test command list. This can be a string, an array of
  strings, or an array of command arrays.

- `test_cmd_timeout`: Fixed timeout for the test suite.

- `build_cmd_timeout`: Timeout for the build command.

- `analyze_cmd`: External command used to parse test output and identify test
  cases.

- `analyze_using_builtin`: Built-in test-output analyzers to use. Accepted
  values are `gtest`, `ctest`, `makefile`, and `test_cmd`.

- `order`: Mutant execution order. Accepted values are `random`,
  `consecutive`, and `bySize`.

- `detected_new_test_case`: Behavior when new test cases are detected.
  Accepted values are `doNothing` and `resetAlive`.

- `detected_dropped_test_case`: Behavior when previously known test cases
  disappear. Accepted values are `doNothing` and `remove`.

- `oldest_mutants`: Behavior for stale mutants when the main worklist is empty.
  Accepted values are `nothing` and `test`.

- `oldest_mutants_nr`: Absolute number of stale mutants to re-test.

- `oldest_mutants_percentage`: Percentage-based form of stale-mutant re-test.

- `parallel_test`: Number of test commands to run in parallel.

- `use_early_stop`: Stop running test commands for a mutant as soon as one
  command fails.

- `continues_check_test_suite`: Periodically re-run the test suite with no
  mutant injected to detect environmental problems.

- `continues_check_test_suite_period`: Number of tested mutants between those
  periodic sanity checks.

- `test_cmd_checksum`: Only run test binaries whose checksum changed after
  mutation.

- `max_test_cmd_output`: Per-test-command output capture limit, in megabytes.

- `max_mem_usage_percentage`: Global host memory usage threshold. When the host
  exceeds this percentage, running test commands may be terminated and retried
  later.

## [report] <a id="config-report"></a>

Default report settings.

- `style`: Default report style. Accepted values are `plain`, `compiler`,
  `json`, and `html`.

- `sections`: Default report sections. Accepted values are `alive`, `killed`,
  `all_mut`, `summary`, `mut_stat`, `tc_killed`, `tc_stat`, `tc_map`,
  `tc_suggestion`, `tc_killed_no_mutants`, `tc_full_overlap`,
  `tc_full_overlap_with_mutation_id`, `tc_groups`, `tc_min_set`,
  `tc_similarity`, `tc_groups_similarity`, `mut_recommend_kill`, `diff`,
  `tc_unique`, `marked_mutants`, and `trend`.

- `high_interest_mutants_nr`: Number of mutants to show in the high-interest
  section.

## [test_group] <a id="test_group"></a>

User-defined report groupings for tests.

- `[test_group.<name>].description`: Human-readable label for the group.

- `[test_group.<name>].pattern`: Regex used to select tests into the group.
  The syntax follows D `std.regex`.

## [test] <a id="config-test"></a>

Extra test metadata used by reports.

- `metadata`: Path to a JSON file containing per-test metadata. The current
  parser understands an array of objects with fields such as `name`, `text`,
  `location.file`, `location.line`, and `redundant`.

## Deprecated compatibility keys

These keys are still recognized for backward compatibility unless otherwise
noted, but new configs should use the replacement shown here.

- `workarea.restrict`: Removed. Use `workarea.exclude` with glob patterns.

- `generic.use_coverage`: Deprecated alias for `coverage.use`.

- `generic.inject_runtime_impl`: Deprecated alias for
  `coverage.inject_runtime_impl`.

- `analyze.mutants_per_schema`: Deprecated alias for
  `schema.mutants_per_schema`.

- `analyze.min_mutants_per_schema`: Deprecated alias for
  `schema.min_mutants_per_schema`.

- `mutant_test.use_schemata`: Deprecated alias for `schema.use`.

- `mutant_test.check_schemata`: Deprecated alias for `schema.check_schemata`.

# Resources

The runtime resources installed with mutate, such as schema and coverage
runtime files, can be overridden by placing replacement files in a higher-
priority data directory.

Dextool searches for data files in this order:

- `$XDG_DATA_HOME/dextool`
- `dirname(<dextool executable>)/data`
- `dirname(dirname(<dextool executable>))/data`
- each entry in `$XDG_DATA_DIRS` as `<dir>/dextool/data`

Mutate resources themselves are resolved under the `mutate/` subdirectory. For
example, overriding the injected schema implementation means providing:

- `$XDG_DATA_HOME/dextool/mutate/schemata_header.c`

or the same relative path inside one of the other higher-priority data search
roots.
