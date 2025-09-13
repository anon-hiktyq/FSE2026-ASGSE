#include <stdio.h>

int mul(int a, int b) {
    int x = a, y = b, prod = 0;

    /*@
    loop invariant x >= 0 && x <= a;
    loop invariant x <= a;
    loop invariant prod == y * (a - x);
    loop invariant prod == a*b - x*y;
    loop invariant prod == (a - x) * y;
    loop invariant prod == (a - x) * b;
    loop invariant prod == (a - x - 1) * b;
    loop invariant 0 <= x;
    loop invariant 0 <= prod;
    loop invariant -1 <= x;
    loop assigns x;
    loop assigns prod;
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