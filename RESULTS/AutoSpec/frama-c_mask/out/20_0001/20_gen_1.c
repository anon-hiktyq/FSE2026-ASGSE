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
                loop invariant 0 <= i < n;
                loop invariant 0 <= j < n;
                loop invariant 2*i <= j;
                loop invariant \forall integer k; 0 <= k < j ==> unknown1() == true;
                loop invariant \forall integer k; j <= k < n; /* Your loop condition for inner "for" */
                loop assigns i;
                loop assigns j;
                loop assigns k;
                */
                for (k = j; k < n; k++) {
                    
                }
            }
            else {
                
            }
        }
    }
END:
    return 0;
}