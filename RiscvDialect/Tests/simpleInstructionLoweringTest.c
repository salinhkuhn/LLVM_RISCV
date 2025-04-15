#include <stdio.h>
#include <stdlib.h>
#include <time.h>
// clang -S -emit-llvm add.c -o add.ll
// clang -S -Xclang -disable-O0-optnone -emit-llvm add.c -o add.ll
// opt -s -O3 add.ll -o add-o3.ll   
// mlir-translate --import-llvm foo.ll -o foo.mlir
        

int64_t add_64(int64_t a, int64_t b) {
    return a + b;
}

int64_t sub_64(int64_t a, int64_t b) {
    return a - b;
}

int64_t mul_64(int64_t a, int64_t b) {
    return a * b;
}

int64_t div_64(int64_t a, int64_t b) {
    return a / b;
}

int64_t rem_64(int64_t a, int64_t b) {
    return a % b;
}


int main () {
    int a = rand();
    int b = rand(); 
    int r1 = add_64(a, b);
    int r2 = sub_64(a, b);
    int r3 = mul_64(a, b);
    int r4 = div_64(a, b);
    int r5 = rem_64(a, b);
}
// add.c
