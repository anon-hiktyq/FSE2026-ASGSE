
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo106(int m,int j,int a) 

            /*@
            Require j < 1 && a <= m
            Ensure Results(__return)
            */
            {

    int k = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((j@pre < 1 && a@pre <= m@pre) => (((k == 0)&&(a == a@pre)&&(j == j@pre)&&(m == m@pre)) || (m >= a && m >= m@pre)) ) &&
((j@pre < 1 && a@pre <= m@pre) => (k >= 0 && k <= 1) ) &&
((j@pre < 1 && a@pre <= m@pre) => (a == a@pre)) &&
((j@pre < 1 && a@pre <= m@pre) => (j == j@pre)
          loop assigns m, k)
    */
    
        while ( k < 1) {

        if(m < a) {
            m = a;
        }
        
        k = k + 1;
    }


}