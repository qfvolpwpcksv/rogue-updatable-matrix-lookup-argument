cmake_minimum_required(VERSION 3.10)
project(LookupArgument)

set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
set(CMAKE_CXX_STANDARD 14)

set(CMAKE_CXX_FLAGS "-w -march=native -O3 -faligned-new -mavx -lgmp -pthread")
set(CMAKE_C_FLAGS "-w -march=native -O3 -faligned-new -mavx -lgmp -pthread")

# set(CMAKE_CXX_FLAGS "-w -march=native -faligned-new -mavx -lgmp -pthread -fsanitize=address,undefined")
# set(CMAKE_C_FLAGS "-w -march=native -faligned-new -mavx -lgmp -pthread -fsanitize=address,undefined")
# set(CMAKE_CXX_FLAGS_DEBUG_INIT "-g -Wall")

link_directories(3rd/mcl)

include_directories(src)
include_directories(3rd)
include_directories(3rd/mcl/include)


include_directories(/usr/local/Cellar/gmp/6.3.0/include) 
link_directories(/usr/local/Cellar/gmp/6.3.0/lib) 

add_subdirectory(src)
add_subdirectory(3rd/mcl)
