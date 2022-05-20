# Build LLVM

1. Clone the `llvm-project` submodule with the following commands.

```
git submodule init
git submodule update
```
2. Navigate to `koi/compiler/submodules/llvm-project`.
3. `mkdir build; cd build`
4. Run the following `cmake` command.
```
cmake -G Ninja ../llvm \
   -DLLVM_TARGETS_TO_BUILD=X86 \
   -DCMAKE_BUILD_TYPE=Release \
   -DLLVM_ENABLE_ASSERTIONS=ON \
   -DCMAKE_EXPORT_COMPILE_COMMANDS=1 \
```
5. Run `ninja` to build LLVM. 
6. Make some tea and wait :)

If you're having trouble with steps 2-6 check our LLVM's [Getting Started](https://llvm.org/docs/GettingStarted.html#getting-started-with-llvm) guide.

# Setup Environment

7. Navigate back to the `koi` directory. 
8. Run the following command to set an environment variable.

```
export KOI_WORKING_DIRECTORY="$(pwd)" && export LLVM_SYS_130_PREFIX="$KOI_WORKING_DIRECTORY/compiler/submodules/llvm-project/build/"
```
