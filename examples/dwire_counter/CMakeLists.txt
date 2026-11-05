cmake_minimum_required(VERSION 3.25)
project(PycircuitDWireCounter LANGUAGES CXX)

find_package(pycircuit CONFIG REQUIRED COMPONENTS Runtime)
include("${PYCIRCUIT_CMAKE_DIR}/PycircuitExamples.cmake")

pycircuit_add_example(dwire_counter
  PACKAGE example_dwire_counter
  TOP example_dwire_counter.dwire_counter.ExerciseDWireCounter
  ENTRY_SOURCE dwire_counter
  CYCLES 5
  SOURCES dwire_counter.py)
