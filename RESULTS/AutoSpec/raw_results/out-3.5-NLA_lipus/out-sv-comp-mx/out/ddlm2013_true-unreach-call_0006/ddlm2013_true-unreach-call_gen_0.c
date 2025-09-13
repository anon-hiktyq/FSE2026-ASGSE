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
    loop invariant a == b + (i - j);
    loop invariant i % 2 == j % 2;
    loop invariant flag ==> a == b + (i - j);
    loop invariant !flag ==> a >= b;
    loop invariant j >= 1;
    loop assigns a, b, i, j;
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