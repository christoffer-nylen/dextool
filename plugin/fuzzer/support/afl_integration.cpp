/// @copyright Boost License 1.0, http://boost.org/LICENSE_1_0.txt
/// @date 2017
/// @author Joakim Brännström (joakim.brannstrom@gmx.com)
/// The license is Boost if nothing else is mentioned.
///
/// This file allows to fuzz libFuzzer-style target functions
/// (LLVMFuzzerTestOneInput) with AFL using AFL's persistent (in-process) mode.
/// The content of the file is divided in two parts, separated by:
///  - ### LLVM ###
///  - ### Dextool ###
/// The code in LLVM is under the LLVM license, the one under Dextool is Boost.
#include "dextool/dextool.hpp"

// ### LLVM ###

// The functions below this point are covered by the following license.
// http://llvm.org/docs/LibFuzzer.html#fuzz-target
// http://llvm.org/docs/LibFuzzer.html#afl-compatibility

//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//===----------------------------------------------------------------------===//

/*
Environment Variables:
There are a few environment variables that can be set to use features that
afl-fuzz doesn't have.

AFL_DRIVER_STDERR_DUPLICATE_FILENAME: Setting this *appends* stderr to the file
specified. If the file does not exist, it is created. This is useful for getting
stack traces (when using ASAN for example) or original error messages on hard to
reproduce bugs.

AFL_DRIVER_EXTRA_STATS_FILENAME: Setting this causes afl_driver to write extra
statistics to the file specified. Currently these are peak_rss_mb
(the peak amount of virtual memory used in MB) and slowest_unit_time_secs. If
the file does not exist it is created. If the file does exist then
afl_driver assumes it was restarted by afl-fuzz and will try to read old
statistics from the file. If that fails then the process will quit.
*/

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <signal.h>
#include <sys/resource.h>
#include <sys/time.h>

#include <iostream>
#include <fstream>
#include <vector>

// Platform detection. Copied from FuzzerInternal.h
#ifdef __linux__
#define LIBFUZZER_LINUX 1
#define LIBFUZZER_APPLE 0
#elif __APPLE__
#define LIBFUZZER_LINUX 0
#define LIBFUZZER_APPLE 1
#else
#error "Support for your platform has not been implemented"
#endif

// Used to avoid repeating error checking boilerplate. If cond is false, a
// fatal error has occured in the program. In this event print error_message
// to stderr and abort(). Otherwise do nothing. Note that setting
// AFL_DRIVER_STDERR_DUPLICATE_FILENAME may cause error_message to be appended
// to the file as well, if the error occurs after the duplication is performed.
#define CHECK_ERROR(cond, error_message)                                       \
    if (!(cond)) {                                                               \
        fprintf(stderr, (error_message));                                          \
        abort();                                                                   \
    }

// libFuzzer interface is thin, so we don't include any libFuzzer headers.
extern "C" {
    int LLVMFuzzerTestOneInput(const uint8_t* Data, size_t Size);
    __attribute__((weak)) int LLVMFuzzerInitialize(int* argc, char** *argv);
}

// Notify AFL about persistent mode.
static volatile char AFL_PERSISTENT[] = "##SIG_AFL_PERSISTENT##";
extern "C" __attribute__((weak)) int __afl_persistent_loop(unsigned int);
static volatile char suppress_warning2 = AFL_PERSISTENT[0];

// Notify AFL about deferred forkserver.
static volatile char AFL_DEFER_FORKSVR[] = "##SIG_AFL_DEFER_FORKSRV##";
extern "C" __attribute__((weak)) void  __afl_manual_init();
static volatile char suppress_warning1 = AFL_DEFER_FORKSVR[0];

// Input buffer.
static const size_t kMaxAflInputSize = 1 << 20;
static uint8_t AflInputBuf[kMaxAflInputSize];

// Variables we need for writing to the extra stats file.
static FILE* extra_stats_file = NULL;
static uint32_t previous_peak_rss = 0;
static time_t slowest_unit_time_secs = 0;
static const int kNumExtraStats = 2;
static const char* kExtraStatsFormatString = "peak_rss_mb            : %u\n"
                                             "slowest_unit_time_sec  : %u\n";

// Copied from FuzzerUtil.cpp.
size_t GetPeakRSSMb() {
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage)) {
        return 0;
    }
    if (LIBFUZZER_LINUX) {
        // ru_maxrss is in KiB
        return usage.ru_maxrss >> 10;
    } else if (LIBFUZZER_APPLE) {
        // ru_maxrss is in bytes
        return usage.ru_maxrss >> 20;
    }
    assert(0 && "GetPeakRSSMb() is not implemented for your platform");
    return 0;
}

// Based on SetSigaction in FuzzerUtil.cpp
static void SetSigaction(int signum,
                         void (*callback)(int, siginfo_t*, void*)) {
    struct sigaction sigact;
    memset(&sigact, 0, sizeof(sigact));
    sigact.sa_sigaction = callback;
    if (sigaction(signum, &sigact, 0)) {
        fprintf(stderr, "libFuzzer: sigaction failed with %d\n", errno);
        exit(1);
    }
}

// Write extra stats to the file specified by the user. If none is specified
// this function will never be called.
static void write_extra_stats() {
    uint32_t peak_rss = GetPeakRSSMb();

    if (peak_rss < previous_peak_rss) {
        peak_rss = previous_peak_rss;
    }

    int chars_printed = fprintf(extra_stats_file, kExtraStatsFormatString,
                                peak_rss, slowest_unit_time_secs);

    CHECK_ERROR(chars_printed != 0, "Failed to write extra_stats_file");

    CHECK_ERROR(fclose(extra_stats_file) == 0,
                "Failed to close extra_stats_file");
}

// Call write_extra_stats before we exit.
static void crash_handler(int, siginfo_t*, void*) {
    // Make sure we don't try calling write_extra_stats again if we crashed while
    // trying to call it.
    static bool first_crash = true;
    CHECK_ERROR(first_crash,
                "Crashed in crash signal handler. This is a bug in the fuzzer.");

    first_crash = false;
    write_extra_stats();
}

// If the user has specified an extra_stats_file through the environment
// variable AFL_DRIVER_EXTRA_STATS_FILENAME, then perform necessary set up
// to write stats to it on exit. If no file is specified, do nothing. Otherwise
// install signal and exit handlers to write to the file when the process exits.
// Then if the file doesn't exist create it and set extra stats to 0. But if it
// does exist then read the initial values of the extra stats from the file
// and check that the file is writable.
static void maybe_initialize_extra_stats() {
    // If AFL_DRIVER_EXTRA_STATS_FILENAME isn't set then we have nothing to do.
    char* extra_stats_filename = getenv("AFL_DRIVER_EXTRA_STATS_FILENAME");
    if (!extra_stats_filename) {
        return;
    }

    // Open the file and find the previous peak_rss_mb value.
    // This is necessary because the fuzzing process is restarted after N
    // iterations are completed. So we may need to get this value from a previous
    // process to be accurate.
    extra_stats_file = fopen(extra_stats_filename, "r");

    // If extra_stats_file already exists: read old stats from it.
    if (extra_stats_file) {
        int matches = fscanf(extra_stats_file, kExtraStatsFormatString,
                             &previous_peak_rss, &slowest_unit_time_secs);

        // Make sure we have read a real extra stats file and that we have used it
        // to set slowest_unit_time_secs and previous_peak_rss.
        CHECK_ERROR(matches == kNumExtraStats, "Extra stats file is corrupt");

        CHECK_ERROR(fclose(extra_stats_file) == 0, "Failed to close file");

        // Now open the file for writing.
        extra_stats_file = fopen(extra_stats_filename, "w");
        CHECK_ERROR(extra_stats_file,
                    "Failed to open extra stats file for writing");
    } else {
        // Looks like this is the first time in a fuzzing job this is being called.
        extra_stats_file = fopen(extra_stats_filename, "w+");
        CHECK_ERROR(extra_stats_file, "failed to create extra stats file");
    }

    // Make sure that crash_handler gets called on any kind of fatal error.
    int crash_signals[] = {SIGSEGV, SIGBUS, SIGABRT, SIGILL, SIGFPE,  SIGINT,
                           SIGTERM
                          };

    const size_t num_signals = sizeof(crash_signals) / sizeof(crash_signals[0]);

    for (size_t idx = 0; idx < num_signals; idx++) {
        SetSigaction(crash_signals[idx], crash_handler);
    }

    // Make sure it gets called on other kinds of exits.
    atexit(write_extra_stats);
}

// If the user asks us to duplicate stderr, then do it.
static void maybe_duplicate_stderr() {
    char* stderr_duplicate_filename =
        getenv("AFL_DRIVER_STDERR_DUPLICATE_FILENAME");

    if (!stderr_duplicate_filename) {
        return;
    }

    FILE* stderr_duplicate_stream =
        freopen(stderr_duplicate_filename, "a+", stderr);

    if (!stderr_duplicate_stream) {
        fprintf(
            stderr,
            "Failed to duplicate stderr to AFL_DRIVER_STDERR_DUPLICATE_FILENAME");
        abort();
    }
}

// Define LLVMFuzzerMutate to avoid link failures for targets that use it
// with libFuzzer's LLVMFuzzerCustomMutator.
extern "C" size_t LLVMFuzzerMutate(uint8_t* Data, size_t Size, size_t MaxSize) {
    assert(false && "LLVMFuzzerMutate should not be called from afl_driver");
    return 0;
}

// ### Dextool ###

namespace dextool {

int afl_main(int argc, char** argv, dextool::DefaultSource** stdin_src) {
    fprintf(stderr,
            "======================= INFO =========================\n"
            "This binary is intended to be used with AFL-fuzz.\n"
            "To run the test cases on specific input(s):\n"
            " %s < INPUT\n"
            "or\n"
            " %s INPUT_FILE1 [INPUT_FILE2...]\n"
            "or to rerun the tests cases for profiling N times\n"
            " %s -N INPUT_FILE1 [INPUT_FILE2...]\n"
            "To fuzz with afl-fuzz:\n"
            " afl-fuzz [afl-flags] %s [-N]\n"
            "afl-fuzz will run N iterations before\n"
            "re-spawning the process (default: 1)\n"
            "======================================================\n",
            argv[0], argv[0], argv[0], argv[0]);
    if (LLVMFuzzerInitialize) {
        LLVMFuzzerInitialize(&argc, &argv);
    }

    maybe_duplicate_stderr();
    maybe_initialize_extra_stats();

    if (__afl_manual_init) {
        __afl_manual_init();
    }

    int N = 1;

    bool has_input_files = false;
    int files_start_at_index = 1;
    for (int i = 1; i < argc; ++i) {
        if (i == 1 && argv[1][0] == '-') {
            N = atoi(argv[1] + 1);
            files_start_at_index = 2;
        } else {
            has_input_files = true;
        }
    }

    if (has_input_files) {
        dextool::execute_all_input_files_one_by_one(argc, argv, files_start_at_index, stdin_src, N);
        return 0;
    }

    assert(N > 0);

    int num_runs = 0;
    dextool::DefaultSource::GuidedType guide_data;

    // either loop as an afl persistent loop or run one time.
    for (; __afl_persistent_loop && __afl_persistent_loop(N) || !__afl_persistent_loop && (num_runs < 1); ++num_runs) {
        dextool::read_stdin(guide_data);
        if (N == 1) {
            std::cerr << "using " << guide_data.size() << " bytes from stdin for fuzzing\n";
        }

        *stdin_src = new dextool::DefaultSource(guide_data);

        dextool::get_fuzz_runner().run();

        delete *stdin_src;
        guide_data.clear();
    }

    std::cerr << argv[0] << ": successfully executed " << num_runs << " input(s)\n";

    return 0;
}

} // NS: dextool
