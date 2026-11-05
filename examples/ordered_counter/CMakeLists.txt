cmake_minimum_required(VERSION 3.25)
project(PycircuitOrderedCounter LANGUAGES CXX)

find_package(pycircuit CONFIG REQUIRED COMPONENTS Runtime)
include("${PYCIRCUIT_CMAKE_DIR}/PycircuitExamples.cmake")

pycircuit_add_example(ordered_counter
  PACKAGE example_ordered_counter
  TOP example_ordered_counter.ordered_counter.ExerciseOrderedCounter
  ENTRY_SOURCE ordered_counter
  CYCLES 4
  SOURCES ordered_counter.py)
