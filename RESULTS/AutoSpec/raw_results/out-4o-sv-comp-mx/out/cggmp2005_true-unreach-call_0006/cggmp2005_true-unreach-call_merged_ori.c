// Source: A. Costan, S. Gaubert, E. Goubault, M. Martel, S. Putot: "A Policy
// Iteration Algorithm for Computing Fixed Points in Static Analysis of
// Programs", CAV 2005

#include "assert.h"

int main() {
    int i,j;
    i = 1;
    j = 10;
    /*@
    loop invariant j >= -1 && j <= 10;
    loop invariant j == 10 - (i - 1) / 2;
    loop invariant j == -1 + (10 - (i - 1) / 2);
    loop invariant j == (10 - (i - 1) / 2);
    loop invariant j <= 10 && 0 <= j;
    loop invariant j + i == 11;
    loop invariant j + i % 2 == 9;
    loop invariant j % 2 == 0;;
    loop invariant j % 2 == 0;
    loop invariant i >= 1 && i % 2 == 1;;
    loop invariant i >= 1 && i % 2 == 1;
    loop invariant i == 2 * (10 - j) + 1;
    loop invariant i == 1 + 2 * ((1 - j) / 3);
    loop invariant i <= j + 2;;
    loop invariant i <= j + 2;
    loop invariant i <= j + 1;
    loop invariant i <= j + 11;
    loop invariant i <= 11;
    loop invariant i - j <= 3;
    loop invariant i - 2 <= j;
    loop invariant i + 2 * j == 21;;
    loop invariant \forall integer k; k >= 0 && 2*k + 1 <= i ==> j == 10 - k;
    loop invariant \forall integer k; 1 <= k <= i ==> k % 2 == 1;
    loop invariant \exists integer k; k >= 0 && i == 1 + 2*k;
    loop invariant \exists integer k; 0 <= k <= i && k % 2 == 1;
    loop invariant 10 - ((i - 1) / 2); <= j;
    loop invariant 1 <= i && i <= 11;
    loop invariant 0; <= j;
    loop invariant (j + i) % 2 == 1;
    loop invariant (i - 1) % 2 == 0;
    loop invariant j <= 10;
    loop invariant i % 2 == 1;
    loop invariant 1 <= i;
    loop invariant 0 <= j;
    loop invariant -1 <= j;
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