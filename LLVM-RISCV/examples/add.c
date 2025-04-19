#include <stdio.h>
#include <stdlib.h>
#include <time.h>
// clang -S -emit-llvm add.c -o add.ll
// clang -S -Xclang -disable-O0-optnone -emit-llvm add.c -o add.ll
// opt -s -O3 add.ll -o add-o3.ll           
int add(int a, int b) {
    return a + b;
}

int64_t add_64(int64_t a, int64_t b) {
    return a + b;
}



int main () {
    int a = rand();
    int b = rand(); 
    return add(a, b);
}
// add.c
