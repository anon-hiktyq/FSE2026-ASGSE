#include <limits.h>
#include "assert.h"

int unknown1();


/* 4. FUNC CONTRACT */
int foo(int k, int n) {
    int i,j;
    //int k,n;
    if( k == n) {
    }
    else {
        goto END;
    }

    /* 3. LOOP INVARIANT */
    for (i = 0; i < n; i++) {
       
        /* 2. LOOP INVARIANT */
        for (j= 2 * i; j < n; j++) {
            if(unknown1()) {
               
                /* 1. LOOP INVARIANT */
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