cmake_minimum_required(VERSION 3.0.0)
project(subgraph_match VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 11)

# find_package(PythonInterp)
# find_package(PythonLibs)

# if(PYTHONLIBS_FOUND)
#     message(STATUS "Library Path = ${PYTHON_LIBRARIES}")
#     message(STATUS "Include Path = ${PYTHON_INCLUDE_DIRS}")
# endif(PYTHONLIBS_FOUND)

include_directories(
    ${CMAKE_SOURCE_DIR}/include
#     ${PYTHON_INCLUDE_DIRS}
)

add_library(${PROJECT_NAME} SHARED
#     c_api.cc
    ${CMAKE_SOURCE_DIR}/src/basic.cpp
    ${CMAKE_SOURCE_DIR}/src/graph.cpp
    ${CMAKE_SOURCE_DIR}/src/io.cpp
    ${CMAKE_SOURCE_DIR}/src/louvain.cpp
    ${CMAKE_SOURCE_DIR}/src/centrality.cpp
)

# target_link_libraries(${PROJECT_NAME} ${PYTHON_LIBRARIES})
