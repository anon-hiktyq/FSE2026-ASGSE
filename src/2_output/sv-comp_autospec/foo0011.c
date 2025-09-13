
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo0011(int n0, int n1) 

            /*@
            Require INT_MIN < n0 && n0 < INT_MAX && INT_MIN < n1 && n1 < INT_MAX
            Ensure Results(__return)
            */
            {
 
  int i0 = 0;
  int k = 0;
 

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n0@pre) => (((k == 0)&&(i0 == 0)&&(n1 == n1@pre)&&(n0 == n0@pre)) || ((k == i0) && (k > 0)))) &&
((0 < n0@pre) => (0 <= i0 && i0 <= n0) ) &&
((0 < n0@pre) => (k == i0) ) &&
((!(0 < n0@pre)) => ((k == 0)&&(i0 == 0)&&(n1 == n1@pre)&&(n0 == n0@pre))) &&
(n1 == n1@pre) &&
(n0 == n0@pre)
    */
    
            while( i0 < n0 ) {
    i0++;
    k++;
  }

  int i1 = 0;
 
 
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv
    (n0 == n0@pre) &&
(n1 == n1@pre)
    */
    
            while( i1 < n1 ) {
    i1++;
    k++;
  }

  int j1 = 0;
  
  
 
  /*@ Print user assertion at number LoopEntry_2*/ 
/*@ Inv emp */ /*2*/ 
 while( j1 < n0 + n1 ) {
    
    j1++;
    k--;
  }
}