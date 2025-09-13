#include <stdio.h>

int mul(int a, int b) {
    int x = a, y = b, prod = 0;

    /*@
    loop invariant x >= 0;
    loop invariant prod == (a - x) * b;
    loop invariant x <= a;
    loop assigns prod, x;
    */
    while(x >= 0) {
        prod = prod + y;
        x--;
    }
    return prod;
}

int main() {
    int pdt = mul(2, 5);
    // @ assert pdt == 10;
}