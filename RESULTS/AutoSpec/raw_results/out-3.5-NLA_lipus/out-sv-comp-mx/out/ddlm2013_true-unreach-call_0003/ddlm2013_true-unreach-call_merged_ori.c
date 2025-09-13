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
    loop invariant i >= 0 && j >= 1 && a >= 0 && b >= 0;
    loop invariant i == 2 * a + (flag ? 0 : 1);
    loop invariant i == (flag ? 2 * a : 2 * a + 1);
    loop invariant i <= j;
    loop invariant i % 2 == 0 || i % 2 == 1;
    loop invariant i % 2 == 0 || i % 2 != 0;
    loop invariant i % 2 == (flag ? 0 : 1);
    loop invariant b == a - (j - i);
    loop invariant b == a - (j - i) * (a / 2);
    loop invariant b == a * j - a * i;
    loop invariant b == a * (j - i);
    loop invariant b == a * (j - i) / 2;
    loop invariant b == a * (j - i) / (j - i + 1);;
    loop invariant b == \sum(0, a-1, k -> (j - (i + 2*k)));
    loop invariant b <= a;
    loop invariant b <= a * j;
    loop invariant b + i <= a + j;
    loop invariant a >= 0 && b >= 0;
    loop invariant a == b + (j - i);
    loop invariant a == b + (j - i) * (a / 2);
    loop invariant a == b + ((j - i) * (a > 0 ? a : 0));
    loop invariant a == \at(a, Pre) + b / (j - i);
    loop invariant a % 2 == 0;
    loop invariant \forall integer k; 0 <= k <= a ==> b + k * (j - i) >= 0;
    loop invariant \forall integer k; 0 <= k <= a ==> (b >= k * (j - i));
    loop invariant 0 < j;
    loop invariant (i + j) % 2 == 0;
    loop invariant (i % 2 == 0) || (i % 2 != 0);;
    loop invariant (i % 2 == 0) ==> (j % 2 == 0);
    loop invariant (i % 2 == 0) <==> (j % 2 == 0);
    loop invariant (i % 2 == 0 && j == (i + 2 * a)) || (i % 2 != 0 && j == (i + 2 * a - 1));
    loop invariant (i % 2 == 0 && j % 2 == 0) || (i % 2 != 0 && j % 2 != 0);
    loop invariant (i % 2 != 0) ==> (j % 2 != 0);
    loop invariant (flag && i % 2 == 0) || (!flag && i % 2 != 0);
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