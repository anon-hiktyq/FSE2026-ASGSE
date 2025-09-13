#include <limits.h>
#include "assert.h"

int unknown1();

/*@
requires n < INT_MAX;
*/
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
                loop assigns k;
                */
                for (k = j; k < n; k++) {
                    // @ assert k >= 2*i;
                }
            }
            else {
                // @ assert  k >= n ;
                // @ assert  k <= n ;
            }
        }
    }
END:
    return 0;
}