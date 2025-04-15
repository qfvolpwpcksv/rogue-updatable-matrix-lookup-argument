# Rogue Updatable Matrix Lookup Argument

We tested our code on linux (Ubuntu) and macOS. 

### 1. Build
#### 1.1 Install Dependencies
Install GMP:
* ```sudo apt install libgmp-dev``` on Ubuntu
* ```brew install gmp``` on macOS

Download MCL: 
```
mkdir 3rd
cd 3rd
git clone https://github.com/herumi/mcl
```

#### 1.2 Compile Rogue 
Please compile using CMakeLists.txt. You might need to change CMakeLists.txt to match your gmp install location. 
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

On Ubuntu, compilation might fail with ```_mm512_loadu_epi64(base)```. Changing it to ```_mm512_load_epi64(base)``` solves the problem. 

#### 2. Test
The binary is generated in `./build/src/main`. You can run the following command to evaluate lookup/update of a random table of $n=2^{10}$ rows and $m=2^5$ columns. Please read `./tests/input-ex.txt` if you want to test our lookup argument with different parameters.  
```
./build/src/main tests/input-ex.txt tests/output-ex.txt
```


