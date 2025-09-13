#include <stdio.h>

int func(int c) {
    int x = c;
    int y = 0;

    /*@
    loop invariant x + y == c;
    loop invariant 0 <= x;
    loop invariant 0 <= y;
    loop invariant c >= x;
    loop invariant c >= y;
    loop invariant \exists integer k; k >= 0 && k == y && k + x == c;
    loop invariant x + y == c;
    loop invariant 0 <= y;
    loop assigns y;
    loop assigns x;
    */
    while(x > 0) {
        x = x - 1;
        y = y + 1;
    }
    return y;
}

// write a test
void main() {
    int t = func(5);
    // @ assert t == 5;
}