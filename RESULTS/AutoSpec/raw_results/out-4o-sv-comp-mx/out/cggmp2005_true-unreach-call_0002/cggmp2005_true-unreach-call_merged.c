// Source: A. Costan, S. Gaubert, E. Goubault, M. Martel, S. Putot: "A Policy
// Iteration Algorithm for Computing Fixed Points in Static Analysis of
// Programs", CAV 2005

#include "assert.h"

int main() {
    int i,j;
    i = 1;
    j = 10;
    /*@
    loop invariant j >= 0 && j <= 10;
    loop invariant i >= 1 && i <= 11;
    loop invariant i <= 1 + 2 * (10 - j);
    loop invariant i - j <= 10;
    loop invariant i - 1 <= j;
    loop invariant i + 2 * j == 21;
    loop invariant \forall integer k; 10 >= k >= j ==> k >= i - 1 - 2*(10 - k);
    loop invariant 2 * j + i == 21;
    loop invariant 0 <= i;
    loop invariant j <= 10;
    loop invariant i == 1 + 2 * (10 - j);
    loop invariant i <= 11;
    loop invariant i % 2 == 1;
    loop invariant 1 <= i;
    loop invariant 0 <= j;
    loop assigns j;
    loop assigns i;
    */
    while (j >= i) {
        i = i + 2;
        j = -1 + j;
    }
    // @ assert j == 6;
    return 0;
}