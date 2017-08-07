# - Find the dynamic lib for libclang and llvm.
#
# llvm-d version requirements:
# The identifier to set the LLVM version is defined as
# `LLVM_{MAJOR_VERSION}_{MINOR_VERSION}_{PATCH_VERSION}`, so to get LLVM
# version 3.1.0 use `LLVM_3_1_0`.
#
# The following variables are defined:
#   LIBCLANG_LDFLAGS    - flags to use when linking
#   LIBLLVM_LDFLAGS     - flags to use when linking
#   LIBLLVM_CXX_FLAGS   - the required flags to build C++ code using LLVM
#   LIBLLVM_FLAGS       - the required flags by llvm-d such as version

execute_process(COMMAND llvm-config --ldflags
    OUTPUT_VARIABLE llvm_config_LDFLAGS
    RESULT_VARIABLE llvm_config_LDFLAGS_status)

execute_process(COMMAND llvm-config --libs --system-libs
    OUTPUT_VARIABLE llvm_config_LIBS
    RESULT_VARIABLE llvm_config_LIBS_status)

execute_process(COMMAND llvm-config --version
    OUTPUT_VARIABLE llvm_config_VERSION
    RESULT_VARIABLE llvm_config_VERSION_status)

execute_process(COMMAND llvm-config --includedir
    OUTPUT_VARIABLE llvm_config_INCLUDE
    RESULT_VARIABLE llvm_config_INCLUDE_status)

execute_process(COMMAND llvm-config --libdir
    OUTPUT_VARIABLE llvm_config_LIBDIR
    RESULT_VARIABLE llvm_config_LIBDIR_status)

string(STRIP "${llvm_config_LDFLAGS}" llvm_config_LDFLAGS)
string(STRIP "${llvm_config_LIBS}" llvm_config_LIBS)
string(STRIP "${llvm_config_VERSION}" llvm_config_VERSION)
string(STRIP "${llvm_config_INCLUDE}" llvm_config_INCLUDE)
string(STRIP "${llvm_config_LIBDIR}" llvm_config_LIBDIR)
message(STATUS "llvm-config VERSION: ${llvm_config_VERSION}")
message(STATUS "llvm-config LIBDIR: ${llvm_config_LIBDIR}")
message(STATUS "llvm-config LDFLAGS: ${llvm_config_LDFLAGS}")
message(STATUS "llvm-config INCLUDE: ${llvm_config_INCLUDE}")
message(STATUS "llvm-config LIBS: ${llvm_config_LIBS}")

# libCLANG ===================================================================

function(try_clang_from_user_config)
    if (LIBCLANG_LIB AND LIBCLANG_LDFLAGS)
        set(LIBCLANG_CONFIG_DONE YES CACHE bool "CLANG Configuration status" FORCE)
        message("Detected user configuration of CLANG")
    endif()
endfunction()

function(try_find_libclang)
    if (llvm_config_LDFLAGS_status OR llvm_config_LIBS_status OR llvm_config_VERSION_status OR llvm_config_INCLUDE_status OR llvm_config_LIBDIR_status)
        return()
    endif()

    set(possible_paths
        "${llvm_config_LIBDIR}"
        # Ubuntu
        "/usr/lib/llvm-4.0/lib"
        "/usr/lib/llvm-3.9/lib"
        "/usr/lib/llvm-3.8/lib"
        "/usr/lib/llvm-3.7/lib"
        # MacOSX
        "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib"
        "/Applications/Xcode.app/Contents/Frameworks"
        # fallback
        "/usr/lib64/llvm"
        )

    # will only try to find if the user has NOT set it
    find_library(LIBCLANG_LIB_PATH
        NAMES clang
        PATHS ${possible_paths}
        )

    if(LIBCLANG_LIB_PATH STREQUAL "LIBCLANG_LIB_PATH-NOTFOUND")
        message(FATAL_ERROR " libclang.so not found")
    endif()

    get_filename_component(LIBCLANG_LIB ${LIBCLANG_LIB_PATH} NAME)

    # -rpath is relative path for all linked libraries.
    # The second "." is argument to rpath.
    if(APPLE)
        set(LIBCLANG_LDFLAGS_OS "-L-rpath -L${llvm_config_LIBDIR} -L-lclang")
    elseif(UNIX)
        set(LIBCLANG_LDFLAGS_OS "-L--enable-new-dtags -L-rpath=${llvm_config_LIBDIR} -L--no-as-needed -L-l:${LIBCLANG_LIB}")
    else()
    endif()

    set(LIBCLANG_LDFLAGS "-L-L${llvm_config_LIBDIR} ${LIBCLANG_LDFLAGS_OS}" CACHE string "Linker flangs for libclang")
    set(LIBCLANG_CONFIG_DONE YES CACHE bool "CLANG Configuration status" FORCE)
endfunction()

# === RUNNING ===

set(LIBCLANG_CONFIG_DONE NO CACHE bool "CLANG Configuration status")
try_clang_from_user_config()
if (NOT LIBCLANG_CONFIG_DONE)
    try_find_libclang()
endif()

# LLVM =======================================================================

function(try_llvm_config_find)
    if (llvm_config_LDFLAGS_status OR llvm_config_LIBS_status OR llvm_config_VERSION_status OR llvm_config_INCLUDE_status OR llvm_config_LIBDIR_status)
        return()
    endif()

    string(TOUPPER "${llvm_config_VERSION}" step2_LLVM_CONF_as_upper)
    string(REGEX REPLACE "[.]" "_" step3_LLVM_VERION "${step2_LLVM_CONF_as_upper}")
    set(LIBLLVM_VERSION "LLVM_${step3_LLVM_VERION}" CACHE "libLLVM version" string)

    # -rpath is relative path for all linked libraries.
    # The second "." is argument to rpath.
    if(APPLE)
        set(llvm_LDFLAGS_OS "-L-rpath -L${llvm_config_LIBDIR} -L-lLLVM")
    elseif(UNIX)
        set(llvm_LDFLAGS_OS "-L--enable-new-dtags -L-rpath=${llvm_config_LIBDIR} -L--no-as-needed")
    endif()

    string(REPLACE "\n" " " llvm_config_LIBS_nonewline "${llvm_config_LIBS}")
    string(REPLACE " " ";" llvm_config_LIBS_aslist "${llvm_config_LIBS_nonewline}")
    set(llvm_config_LIBS "")
    foreach (var ${llvm_config_LIBS_aslist})
        string(STRIP "${var}" var)
        if (var)
            set(llvm_config_LIBS "${llvm_config_LIBS} -L${var}")
        endif()
    endforeach()

    set(LIBLLVM_LDFLAGS "-L${llvm_config_LDFLAGS} ${llvm_LDFLAGS_OS} ${llvm_config_LIBS}" CACHE string "Linker flags for libLLVM")

    set(LIBLLVM_CXX_FLAGS "-I${llvm_config_INCLUDE} -std=c++0x -fno-exceptions -fno-rtti " CACHE string "Compiler flags for C++ using LLVM")
    set(LIBLLVM_CONFIG_DONE YES CACHE bool "LLVM Configuration status" FORCE)
endfunction()

function(try_llvm_from_user_config)
    if (LIBLLVM_LDFLAGS AND LIBLLVM_FLAGS AND LIBLLVM_CXX_FLAGS)
        set(LIBLLVM_CONFIG_DONE YES CACHE bool "LLVM Configuration status" FORCE)
        message("Detected user configuration of LLVM")
    endif()
endfunction()

# === RUNNING ===

set(LIBLLVM_CONFIG_DONE NO CACHE bool "LLVM Configuration status")
try_llvm_from_user_config()
if (NOT LIBLLVM_CONFIG_DONE)
    try_llvm_config_find()
endif()

# Fixup
# Simplify to only support x86
set(LIBLLVM_TARGET "LLVM_Target_X86")
set(LIBLLVM_FLAGS "-version=${LIBLLVM_VERSION} -version=${LIBLLVM_TARGET}" CACHE string "D version flags for libLLVM")

message(STATUS "libclang config status : ${LIBCLANG_CONFIG_DONE}")
message(STATUS "libclang linker flags: ${LIBCLANG_LDFLAGS}")

message(STATUS "libLLVM config status: ${LIBLLVM_CONFIG_DONE}")
message(STATUS "libLLVM D flags: ${LIBLLVM_FLAGS}")
message(STATUS "libLLVM CXX flags: ${LIBLLVM_CXX_FLAGS}")
message(STATUS "libLLVM linker flags: ${LIBLLVM_LDFLAGS}")
