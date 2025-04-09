cmake_minimum_required(VERSION 3.13)

project(swine-z3)

set(CMAKE_CXX_STANDARD 20)

set(EXECUTABLE swine-z3)

set(CMAKE_LIBRARY_PATH $ENV{LD_LIBRARY_PATH})

option(STATIC "enable static build" OFF)

if (${STATIC})
    message(STATUS "Configuring static build")
    set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
    set(BUILD_SHARED_LIBS OFF)
    add_link_options(-static)
else()
    message(STATUS "Configuring non-static build")
    set(CMAKE_FIND_LIBRARY_SUFFIXES ".so" ".dylib" ".lib" ".a")
    set(BUILD_SHARED_LIBS ON)
    if (UNIX)
        add_compile_options(-fPIC)
    endif()
endif()

set(INCLUDE_DIRS
  "${PROJECT_SOURCE_DIR}/include")

if (UNIX)
   add_compile_options(-Wall -Wextra -pedantic -Wno-unused-parameter)
endif()

set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON)

set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "${CMAKE_CXX_FLAGS_RELEASE} -g")

list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/")
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC SHA)
git_local_changes(DIRTY)

# generate version.cc
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/src/version.cpp.in" "${CMAKE_CURRENT_SOURCE_DIR}/src/version.cpp" @ONLY)

message(STATUS "Build type: " ${CMAKE_BUILD_TYPE})
message(STATUS "Compiler flags:" ${CMAKE_CXX_COMPILE_FLAGS})
message(STATUS "Compiler cxx debug flags:" ${CMAKE_CXX_FLAGS_DEBUG})
message(STATUS "Compiler cxx release flags:" ${CMAKE_CXX_FLAGS_RELEASE})
message(STATUS "Compiler cxx relwithdebinfo flags:" ${CMAKE_CXX_FLAGS_RELWITHDEBINFO})
message(STATUS "Compiler cxx min size flags:" ${CMAKE_CXX_FLAGS_MINSIZEREL})
message(STATUS "Compiler cxx flags:" ${CMAKE_CXX_FLAGS})

find_library(Z3 z3)
message(STATUS "z3: ${Z3}")

add_executable(${EXECUTABLE} "")

set (SOURCES
    "${PROJECT_SOURCE_DIR}/include/swine.h"
    "${PROJECT_SOURCE_DIR}/src/swine.cpp"
    "${PROJECT_SOURCE_DIR}/include/term_evaluator.h"
    "${PROJECT_SOURCE_DIR}/src/term_evaluator.cpp"
    "${PROJECT_SOURCE_DIR}/include/constant_propagator.h"
    "${PROJECT_SOURCE_DIR}/src/constant_propagator.cpp"
    "${PROJECT_SOURCE_DIR}/include/rewriter.h"
    "${PROJECT_SOURCE_DIR}/src/rewriter.cpp"
    "${PROJECT_SOURCE_DIR}/include/preprocessor.h"
    "${PROJECT_SOURCE_DIR}/src/preprocessor.cpp"
    "${PROJECT_SOURCE_DIR}/include/exp_finder.h"
    "${PROJECT_SOURCE_DIR}/src/exp_finder.cpp"
    "${PROJECT_SOURCE_DIR}/include/brute_force.h"
    "${PROJECT_SOURCE_DIR}/src/brute_force.cpp"
    "${PROJECT_SOURCE_DIR}/include/util.h"
    "${PROJECT_SOURCE_DIR}/src/util.cpp"
    "${PROJECT_SOURCE_DIR}/include/lemma_kind.h"
    "${PROJECT_SOURCE_DIR}/src/lemma_kind.cpp"
    "${PROJECT_SOURCE_DIR}/include/preproc_kind.h"
    "${PROJECT_SOURCE_DIR}/src/preproc_kind.cpp"
    "${PROJECT_SOURCE_DIR}/include/config.h"
    "${PROJECT_SOURCE_DIR}/src/config.cpp"
    "${PROJECT_SOURCE_DIR}/include/stats.h"
    "${PROJECT_SOURCE_DIR}/src/stats.cpp"
    "${PROJECT_SOURCE_DIR}/include/term.h"
    "${PROJECT_SOURCE_DIR}/src/term.cpp"
    "${PROJECT_SOURCE_DIR}/include/comparison.h"
    "${PROJECT_SOURCE_DIR}/src/comparison.cpp"
    "${PROJECT_SOURCE_DIR}/include/power_comp.h"
    "${PROJECT_SOURCE_DIR}/src/power_comp.cpp"
    "${PROJECT_SOURCE_DIR}/include/divisibility.h"
    "${PROJECT_SOURCE_DIR}/src/divisibility.cpp"
    "${PROJECT_SOURCE_DIR}/include/eia_proj.h"
    "${PROJECT_SOURCE_DIR}/src/eia_proj.cpp"
    "${PROJECT_SOURCE_DIR}/include/eia_nonlazy.h"
    "${PROJECT_SOURCE_DIR}/src/eia_nonlazy.cpp"
    "${PROJECT_SOURCE_DIR}/include/algorithm.h"
    "${PROJECT_SOURCE_DIR}/src/algorithm.cpp"
    "${PROJECT_SOURCE_DIR}/include/range_utils.h"
    "${PROJECT_SOURCE_DIR}/include/version.h"
    "${PROJECT_SOURCE_DIR}/src/version.cpp"
)

add_library(objlib OBJECT ${SOURCES})

target_sources(${EXECUTABLE} PRIVATE
    $<TARGET_OBJECTS:objlib>
    "${PROJECT_SOURCE_DIR}/src/main.cpp"
)

if (${STATIC})
    add_library(libswine-z3 STATIC $<TARGET_OBJECTS:objlib>)
else()
    add_library(libswine-z3 SHARED $<TARGET_OBJECTS:objlib>)
endif()

set_property(TARGET libswine-z3 PROPERTY OUTPUT_NAME swine-z3)

include_directories(${INCLUDE_DIRS})

target_link_libraries(${EXECUTABLE}
    ${Z3}
)

target_link_libraries(libswine-z3
    ${Z3}
)
