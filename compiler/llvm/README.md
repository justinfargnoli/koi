```
cmake -G Ninja ../llvm \
   -DLLVM_TARGETS_TO_BUILD=X86 \
   -DCMAKE_BUILD_TYPE=Release \
   -DLLVM_ENABLE_ASSERTIONS=ON \
   -DCMAKE_EXPORT_COMPILE_COMMANDS=1 \
```

```
export LLVM_SYS_130_PREFIX="<PATH TO KOI DIRECTORY>/koi/compiler/llvm/llvm-project/build"
```
