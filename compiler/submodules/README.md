# Build LLVM
```
cmake -G Ninja ../llvm \
   -DLLVM_TARGETS_TO_BUILD=X86 \
   -DCMAKE_BUILD_TYPE=Release \
   -DLLVM_ENABLE_ASSERTIONS=ON \
   -DCMAKE_EXPORT_COMPILE_COMMANDS=1 \
```

# Setup Environment
```
export KOI_WORKING_DIRECTORY="$(pwd)" && export LLVM_SYS_130_PREFIX="$KOI_WORKING_DIRECTORY/compiler/submodules/llvm-project/build/"
```
