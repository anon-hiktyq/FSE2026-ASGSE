// Source: Isil Dillig, Thomas Dillig, Boyang Li, Ken McMillan: "Inductive
// Invariant Generation via Abductive Inference", OOPSLA 2013.
#include "assert.h"
int unknown1();

int foo(int flag) {
    unsigned int i,j,a,b;
    a = 0;
    b = 0;
    j = 1;
    if (flag) {
        i = 0;
    } else {
        i = 1;
    }

    /*@
    loop invariant j - i == b - a;
    loop invariant i % 2 == 1 ==> j % 2 == 1;
    loop invariant i % 2 == 0 ==> j >= i;
    loop invariant i % 2 == 0 ==> j % 2 == 0;
    loop invariant i % 2 != 0 ==> j > i;
    loop invariant b == a * (j - i);
    loop invariant b == a * (j - i) / a;
    loop invariant b == a * (j - i) / 2;
    loop invariant b == a * (j - i) / (j - i);
    loop invariant a == b + (j - i);
    loop invariant 1 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant (j >= 1 && i >= 0);
    loop invariant (i >= 0 && j >= 1);
    loop invariant (i % 2 == 0) ==> (j % 2 == 0);
    loop invariant (i % 2 == 0 && j == i + 1) || (i % 2 == 1 && j == i);
    loop invariant (i % 2 == 0 && j % 2 == 0) || (i % 2 == 1 && j % 2 == 1);
    loop invariant (i % 2 == 0 && j % 2 == 0) || (i % 2 != 0 && j % 2 != 0);
    loop invariant (i % 2 != 0) ==> (j % 2 != 0);
    loop invariant (flag ? 0 : 1) <= i;
    loop assigns j;
    loop assigns i;
    loop assigns b;
    loop assigns a;
    ```c;
    ```;
    */
    while (unknown1()) {
        a++;
        b += (j - i);
        i += 2;
        if (i%2 == 0) {
            j += 2;
        } else {
            j++;
        }
    }
    if (flag) {
        // @ assert a == b;
    }
    return 0;
}