#include <stdio.h>

int mul(int a, int b) {
    int x = a, y = b, prod = 0;

    /*@
    loop invariant x + 1 <= a + 1;
    loop invariant prod == (a - x) * b;
    loop invariant x >= 0;
    loop invariant prod >= 0;
    loop invariant \forall integer k; (a - x) <= k <= a ==> prod == k * b;
    loop invariant x <= a;
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