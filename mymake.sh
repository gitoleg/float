#!/bin/bash

llvm_sys_flags=`llvm-config --system-libs`
llvm_ldflags=`llvm-config --ldflags`
llvm_cxxflags=`llvm-config --cxxflags`
llvm_cflags=`llvm-config --cflags`
llvm_libs=`llvm-config --libs`

clang++ test.cpp -o test $llvm_cxxflags -lstdc++  $llvm_ldflags $llvm_sys_flags $llvm_cflags $llvm_libs
