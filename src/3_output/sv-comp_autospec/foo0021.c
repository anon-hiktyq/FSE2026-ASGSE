
#include <limits.h>

int unknown1();

/*@
requires n < INT_MAX;
requires k == n;
*/
int foo0021(int k, int n) {
    int i, j;

    i = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    */
    for (; i < n; i++) {
        j = 2*i;
        
        /*@
        */
        for (; j < n; j++) {
            if(unknown1()) {
                
               /*@ assert \forall integer k; j <= k < n ==> k >= 2*i; */
            }
            else {
                /*@ assert k == n; */
            }
        }
    }
}
