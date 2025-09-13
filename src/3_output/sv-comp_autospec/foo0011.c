
#include <limits.h>

/*@
requires INT_MIN < n0 && n0 < INT_MAX;
requires INT_MIN < n1 && n1 < INT_MAX;
*/
void foo0011(int n0, int n1) {
 
  int i0 = 0;
  int k = 0;
 

  
            
            /*@
          loop invariant (0 < \at(n0,Pre)) ==> (((k == 0)&&(i0 == 0)&&(n1 == \at(n1,Pre))&&(n0 == \at(n0,Pre))) || ((k == i0) && (k > 0)));
          loop invariant (0 < \at(n0,Pre)) ==> (0 <= i0 <= n0) ;
          loop invariant (0 < \at(n0,Pre)) ==> (k == i0) ;
          loop invariant (!(0 < \at(n0,Pre))) ==> ((k == 0)&&(i0 == 0)&&(n1 == \at(n1,Pre))&&(n0 == \at(n0,Pre)));
          loop invariant n1 == \at(n1,Pre);
          loop invariant n0 == \at(n0,Pre);
            */
            while( i0 < n0 ) {
    i0++;
    k++;
  }
            

  int i1 = 0;
 
  
            
            /*@
          loop invariant n0 == \at(n0,Pre);
          loop invariant n1 == \at(n1,Pre);
            */
            while( i1 < n1 ) {
    i1++;
    k++;
  }
            

  int j1 = 0;
  
  
  
            
            /*@
          loop invariant 0 <= j1 <= n0 + n1;
          loop invariant k == n0 + n1 - j1;
          loop invariant j1 < n0 + n1 ==> k > 0;
          loop invariant n0 == \at(n0,Pre);
          loop invariant n1 == \at(n1,Pre);
            */
            while( j1 < n0 + n1 ) {
    /*@ assert k>0;*/
    j1++;
    k--;
  }
            
}
