
#include <limits.h>

int unknown1();

/*@
requires n < INT_MAX;
requires k == n;
*/
int foo0021(int k, int n) {
    int i,j;

    i = 0;

    /*@
    loop invariant 0 <= i <= n;
    loop invariant j == 2*i;
    loop invariant i <= n;
    loop invariant \forall integer m; 0 <= m < i ==> 2*m < n;
    loop assigns i;
    loop assigns j;
    */
    for (; i < n; i++) {
        
        j = 2*i;
        
        /*@
        loop invariant j <= n;
        loop invariant i <= n;
        loop invariant i < n;
        loop invariant \forall integer m; j <= m < n ==> m >= 2*i;
        loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
        loop invariant \forall integer k; j <= k < n ==> k >= 2 * i;
        loop invariant \forall integer k; j <= k < n ==> k <= n && k >= 2 * i;
        loop invariant \forall integer k; i <= k < n ==> k == n;
        loop invariant \forall integer k; 0 <= k < i ==> 2*k <= j;
        loop invariant 2*i <= j;
        loop invariant 2 * i <= j;
        loop invariant 0 <= j;
        loop invariant 0 <= i;
        loop assigns k;
        loop assigns j;
        loop assigns i;
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
