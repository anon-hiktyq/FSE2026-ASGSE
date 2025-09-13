
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
    loop invariant j < n ==> \forall integer q; j <= q < n ==> q >= 2 * i;
    loop invariant i < n ==> \forall integer p; i <= p < n ==> p >= i;
    loop invariant \forall integer x; i <= x < n ==> 2 * i <= 2 * x;
    loop invariant \forall integer x; 0 <= x < i ==> 2 * x < n;
    loop invariant \forall integer x, y; 0 <= x < i && i <= y < n ==> 2 * x < 2 * y;
    loop invariant \forall integer p; 0 <= p < i ==> 2 * p < n;
    loop invariant \forall integer k; j <= k < n ==> k >= 2 * i;
    loop invariant \forall integer k; 0 <= k < i ==> \forall integer m; 2 * k <= m < n ==> m >= 2 * k;
    loop invariant \forall integer k; 0 <= k < i ==> 2 * k < n;
    loop invariant 2 * i <= j;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns j;
    loop assigns i;
    */
    for (; i < n; i++) {
        
        j = 2*i;
        
        /*@
        loop invariant j <= n;
        loop invariant i <= n;
        loop invariant i < n;
        loop invariant i < n ==> \forall integer k; j <= k < n ==> k >= 2*i;
        loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
        loop invariant \forall integer k; j <= k < n ==> k >= 2 * i;
        loop invariant \forall integer k; 2 * i <= k < j ==> k >= 2 * i;
        loop invariant \forall integer k; 0 <= k < i ==> 2 * k < n;
        loop invariant \forall integer k; 0 <= k < i && 2 * k < n;
        loop invariant 2*i <= j;
        loop invariant 2 * i <= j;
        loop invariant 0 <= j;
        loop invariant 0 <= i;
        loop assigns j;
        loop assigns i;
        */
        for (; j < n; j++) {
            if(unknown1()) {
                
            }
            else {
                // @ assert k>=n && k <= n;*/
            }
        }
    }
}
