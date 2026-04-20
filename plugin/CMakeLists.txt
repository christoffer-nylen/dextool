# vim: filetype=cmake

option(DEXTOOL_BUILD_PLUGIN_ANALYZE "Build the dextool analyze plugin" OFF)
option(DEXTOOL_BUILD_PLUGIN_CTESTDOUBLE "Build the dextool ctestdouble plugin" ON)
option(DEXTOOL_BUILD_PLUGIN_CPPTESTDOUBLE "Build the dextool cpptestdouble plugin" ON)
option(DEXTOOL_BUILD_PLUGIN_EXAMPLE "Build the dextool example plugin" OFF)
option(DEXTOOL_BUILD_PLUGIN_MUTATE "Build the dextool mutate plugin" ON)
option(DEXTOOL_BUILD_PLUGIN_UML "Build the dextool uml plugin" OFF)

if(DEXTOOL_BUILD_PLUGIN_ANALYZE)
    add_subdirectory(analyze)
endif()

if(DEXTOOL_BUILD_PLUGIN_CTESTDOUBLE)
    add_subdirectory(ctestdouble)
endif()

if(DEXTOOL_BUILD_PLUGIN_CPPTESTDOUBLE)
    add_subdirectory(cpptestdouble)
endif()

if(DEXTOOL_BUILD_PLUGIN_EXAMPLE)
    add_subdirectory(example)
endif()

if(DEXTOOL_BUILD_PLUGIN_UML)
    add_subdirectory(uml)
endif()

if(DEXTOOL_BUILD_PLUGIN_MUTATE)
    add_subdirectory(mutate)
endif()
