
#include <limits.h>

int unknown1();

/*@
requires n < INT_MAX;
requires k == n;
*/
int foo0021(int k, int n) {
    int i,j;

    i = 0;

    for (; i < n; i++) {
        
        j = 2*i;
        
        /*@
        loop invariant 0 <= j <= n;
        loop invariant j >= 2*i;
        loop invariant i < n ==> \forall integer k; j <= k < n ==> k >= 2*i;
        loop assigns j;
        */
        for (; j < n; j++) {
            if(unknown1()) {
                
               /*@ forall integer k; j <= k < n; k >= 2*i; */
            }
            else {
                // @ assert k>=n && k <= n;*/
            }
        }
    }
}
