
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
    loop invariant k == n;
    loop invariant 0 <= j <= n;
    loop invariant \forall integer m; 0 <= m < i ==> 2 * m <= n;
    loop invariant \forall integer m; i <= m < n ==> 2 * i <= m;
    loop assigns i;
    loop assigns j;
    */
    for (; i < n; i++) {
        
        j = 2*i;
        
        /*@
        loop invariant k == n;
        loop invariant j <= n;
        loop invariant i <= n;
        loop invariant \forall integer m; i <= m < n ==> 2*i <= j <= n;
        loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
        loop invariant \forall integer k; j <= k < n ==> k >= 2 * i;
        loop invariant \forall integer k; 0 <= k < i ==> \forall integer m; 2 * k <= m < n;
        loop invariant 2*i <= j;
        loop invariant 2 * i <= j;
        loop invariant 0 <= j;
        loop invariant 0 <= i;
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
