#include <limits.h>
#include "assert.h"

int __BLAST_NONDET;

/*@
requires INT_MIN < n && n < INT_MAX;
requires INT_MIN < m && m < INT_MAX;
requires INT_MIN < l && l < INT_MAX;
*/
int foo(int n, int m , int l) {
    int i,j,k;
    //int n,l,m;
    if(3*n<=m+l); else goto END;
    for (i=0;i<n;i++)
        for (j = 2*i;j<3*i;j++)
            /*@
            loop invariant k <= j;
            loop invariant k - i <= 2*n;
            loop invariant k - i <= 2 * n;
            loop invariant j <= 3*i;
            loop invariant j <= 3 * i;
            loop invariant i <= n;
            loop invariant i <= k;
            loop invariant 3 * n <= m + l;
            loop invariant 2*i <= j;
            loop invariant 2 * i <= j;
            loop invariant 0 <= k;
            loop invariant 0 <= j;
            loop invariant 0 <= i;
            loop assigns k;
            */
            for (k = i; k< j; k++) {
                // @ assert  k-i <= 2*n ;
            }
END:
    return 0;
}