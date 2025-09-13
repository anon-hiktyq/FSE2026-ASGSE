
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
      loop invariant (0 < \at(n,Pre)) ==> (i <= n) ;
      loop invariant (!(0 < \at(n,Pre))) ==> ((i == 0)&&(n == \at(n,Pre))&&(k == \at(n,Pre))) ;
      loop invariant n == \at(n,Pre);
      loop invariant k == \at(k,Pre);
    */
    for (; i < n; i++) {
        
        j = 2*i;
        
        /*@
          loop invariant 2*i <= j < n;
        */
        for (; j < n; j++) {
            if(unknown1()) {
                
               /*@ 
                 loop invariant \forall integer k; j <= k < n ==> k >= 2*i;
               */
            }
            else {
                /*@ assert k>=n && k <= n;*/
            }
        }
            
    }
}
