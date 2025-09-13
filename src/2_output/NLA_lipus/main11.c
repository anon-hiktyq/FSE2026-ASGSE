
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main11(int z,int k,int a)

            /*@
            Require z >= 0 && z <= 10 && k > 0 && k <= 10
            Ensure Results(__return)
            */
            {
  

    int x=a;
    int y=1;
    int c=1;
  
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((1 < k@pre) => (z*x - x + a - a*z*y == 0)) &&
((1 < k@pre) => (c >= 1 && c <= k)) &&
((!(1 < k@pre)) => ((c == 1)&&(y == 1)&&(x == a@pre)&&(a == a@pre)&&(k == k@pre)&&(z == z@pre))) &&
(a == a@pre) &&
(k == k@pre) &&
(z == z@pre
          loop assigns c, x, y)
    */
    
            while (c < k){
   c = c + 1;
   x = x*z + a;
   y = y*z;
    }
  
  
  }