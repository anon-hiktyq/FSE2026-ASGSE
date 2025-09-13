#include <limits.h>
#include "assert.h"

int unknown1();


int foo(int k, int n) {
    int i,j;
    //int k,n;
    if( k == n) {
    }
    else {
        goto END;
    }

    for (i = 0; i < n; i++) {
       
        for (j= 2 * i; j < n; j++) {
            if(unknown1()) {
               
                /*@
                loop invariant j < n;
                loop invariant j - 2 * i < n;
                loop invariant i < n;
                loop invariant \forall integer m; 0 <= m < j ==> (k >= m);
                loop invariant \forall integer k; j <= k;
                loop invariant 2*i <= j;
                loop invariant 2 * i <= j;
                loop invariant 0 <= j;
                loop invariant 0 <= i;
                loop assigns k;
                loop assigns j;
                loop assigns i;
                */
                for (k = j; k < n; k++) {
                     //@ assert k >= 2*i;
                }
            }
            else {
                //@ assert  k >= n ;
                //@ assert  k <= n ;
                
            }
        }
    }
END:
    return 0;
}