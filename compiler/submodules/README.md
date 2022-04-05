# Build LLVM
```
cmake -G Ninja ../llvm \
   -DLLVM_TARGETS_TO_BUILD=X86 \
   -DCMAKE_BUILD_TYPE=Release \
   -DLLVM_ENABLE_ASSERTIONS=ON \
   -DCMAKE_EXPORT_COMPILE_COMMANDS=1 \
   -DLLVM_ENABLE_FFI=ON \
```

# Setup Environment
```
export KOI_WORKING_DIRECTORY="$(pwd)" && export LLVM_SYS_130_PREFIX="$KOI_WORKING_DIRECTORY/compiler/llvm/llvm-project/build/"
```
