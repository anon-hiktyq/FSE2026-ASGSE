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
               
                /* @ >>> INFILL <<< */
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