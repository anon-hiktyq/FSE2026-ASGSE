
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
    loop invariant j == 2 * i;
    loop invariant j <= n;
    loop invariant i <= n;
    loop invariant i <= j;
    loop invariant \forall integer k; j <= k < n ==> k >= 2 * i;
    loop invariant \forall integer k; i <= k < n ==> k >= 2 * i;
    loop invariant \forall integer k; i <= k < n ==> (k >= 2 * i);
    loop invariant \forall integer k; 0 <= k < j ==> k >= 2 * i;
    loop invariant \forall integer k; 0 <= k < i ==> k < n;
    loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; 2 * k <= l < n;
    loop invariant \forall integer k; 0 <= k < i ==> 2 * k < n;
    loop invariant \forall integer k; 0 <= k < i ==> (\forall integer l; 2 * k <= l < n ==> l >= 2 * k);
    loop invariant 2 * i <= j;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns j;
    loop assigns i;
    ```c;
    ```;
    */
    for (; i < n; i++) {
        
        j = 2*i;
        
        /*@
        loop invariant j <= n;
        loop invariant i <= n;
        loop invariant i <= j;
        loop invariant i < n;
        loop invariant i < INT_MAX;
        loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
        loop invariant \forall integer k; i <= k < n ==> (k >= 2 * i);
        loop invariant \forall integer k; 0 <= k < j ==> k >= 2 * i;
        loop invariant \forall integer k; 0 <= k < i ==> k < n;
        loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; 2 * k <= l < n;
        loop invariant \forall integer k; 0 <= k < i ==> (2 * k < j);
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
