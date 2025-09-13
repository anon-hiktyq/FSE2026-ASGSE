
#include <limits.h>

/*@
requires n <= INT_MAX;
*/
void foo0019(int n) {
  int i,k;
  k = n;
  i = 0;

  
  
            
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (((k == \at(n,Pre))&&(i == 0)&&(n == \at(n,Pre))) || (k + i/2 == \at(n,Pre)));
          loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= 2*\at(n,Pre) && i % 2 == 0) ;
          loop invariant (0 < \at(n,Pre)) ==> (k == \at(n,Pre) - i/2) ;
          loop invariant (!(0 < \at(n,Pre))) ==> ((k == \at(n,Pre))&&(i == 0)&&(n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
            */
            while( i < n ) {
    k--;
    i = i + 2;
  }
            

  int j = 0;

  
  
            
            /*@
          loop invariant k == n - i/2 - j;
          loop invariant 0 <= j && (n > 0 ==> j <= n/2);
            */
            while( j < n/2 ) {
    /*@ assert k > 0; */
    k--;
    j++;
  }
            
}
