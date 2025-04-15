## Rogue Updatable Matrix Lookup Argument

To test our lookup argument: 

#### 1. Build
Download MCL:  
```
mkdir 3rd
cd 3rd
git clone https://github.com/herumi/mcl
```
Compile using CMakeLists.txt. You might need to change CMakeLists.txt to match your gmp install location. 
```
mkdir build
cd build
cmake ..
make -j4
```
clang++ is required except for x86-64 on Linux and Windows.
```
make -j4 CXX=clang++
```

#### 2. Test
```
./build/src/main tests/input-ex.txt tests/output-ex.txt
```
