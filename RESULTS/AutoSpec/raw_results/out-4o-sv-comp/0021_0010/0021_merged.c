
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
    loop invariant k == n;
    loop invariant j <= n;
    loop invariant i <= n;
    loop invariant \forall integer m; i <= m < n ==> 2*i <= j <= n;
    loop invariant \forall integer m; i <= m < n ==> 2 * i <= m;
    loop invariant \forall integer m; 0 <= m < i ==> \forall integer l; 2*m <= l < n;
    loop invariant \forall integer m; 0 <= m < i ==> 2*m <= n;
    loop invariant \forall integer m; 0 <= m < i ==> 2 * m <= n;
    loop invariant \forall integer m; 0 <= m < i ==> (2*m <= j < n);
    loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns j;
    loop assigns i;
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
                
            }
            else {
                // @ assert k>=n && k <= n;*/
            }
        }
    }
}
