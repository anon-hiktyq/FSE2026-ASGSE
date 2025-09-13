
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
    ```c
    loop invariant 0 <= i <= n;
    loop invariant 0 <= j <= n;
    loop invariant \forall integer x; 0 <= x < i ==> 2 * x < n;
    loop invariant \forall integer x; i <= x < n ==> 2 * i <= 2 * x;
    loop invariant \forall integer x, y; 0 <= x < i && i <= y < n ==> 2 * x < 2 * y;
    loop assigns i, j;
    ```
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
                
               /*@ forall integer k; j <= k < n; k >= 2*i; */
            }
            else {
                // @ assert k>=n && k <= n;*/
            }
        }
    }
}
