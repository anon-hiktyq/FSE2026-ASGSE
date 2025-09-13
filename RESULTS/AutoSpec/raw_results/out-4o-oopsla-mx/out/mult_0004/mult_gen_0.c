#include <stdio.h>

int mul(int a, int b) {
    int x = a, y = b, prod = 0;

    /*@
    loop invariant x >= 0;
    loop invariant prod == (a - x) * b;
    loop invariant prod == x * y + (a - x) * y;
    loop invariant prod == y * a - y * x;
    loop invariant \forall integer k; 0 <= k <= a - x ==> prod == k * b;
    loop invariant y == b;
    loop invariant x <= a;
    loop invariant prod == a * b - x * b;
    loop invariant prod == (a - x) * y;
    loop invariant prod == (a - x) * b;
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