#include <stdio.h>

int mul(int a, int b) {
    int x = a, y = b, prod = 0;

    /*@
    loop invariant x >= 0 ==> prod >= 0;
    loop invariant x + prod / b == a;
    loop invariant x + 1 <= a + 1;
    loop invariant x + (prod / b) == a;
    loop invariant prod == y * (a - x);
    loop invariant prod <= a * b;
    loop invariant prod % b == 0;
    loop invariant \forall integer k; 0 <= k <= a - x ==> prod == k * b;
    loop invariant \forall integer k; (a - x) <= k <= a ==> prod == k * b;
    loop invariant 0 <= x;
    loop invariant 0 <= prod;
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