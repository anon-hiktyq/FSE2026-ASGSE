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
    loop invariant (i % 2 == 0 && j % 2 == 0) || (i % 2 != 0 && j % 2 != 0);
    loop invariant b == a * (j - i);
    loop invariant a == \at(a, Pre) + b / (j - i);
    loop invariant \forall integer k; 0 <= k <= a ==> (b >= k * (j - i));
    loop invariant i >= 0 && j >= 1 && a >= 0 && b >= 0;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant (i % 2 == 0) || (i % 2 != 0);
    loop assigns j;
    loop assigns i;
    loop assigns b;
    loop assigns a;
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