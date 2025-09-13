
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
        loop invariant 2*i <= j <= n;
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
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
