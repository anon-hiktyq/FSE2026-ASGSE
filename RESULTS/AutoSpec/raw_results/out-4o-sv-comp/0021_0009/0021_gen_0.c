
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
        ```c
        loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= n;
        loop invariant j >= 2 * i;
        loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; 2*k <= l < n ==> unknown1() || (k >= n && k <= n);
        loop assigns i, j;
        ```
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
