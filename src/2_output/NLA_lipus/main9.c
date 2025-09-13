
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main9(int z,int k)

            /*@
            Require z >= 0 && z <= 10 && k > 0 && k <= 10
            Ensure Results(__return)
            */
            {
  

  int x=1;
  int y=z;
  int c=1;

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((1 < k@pre) => (x*z - x - y + 1 == 0)) &&
((1 < k@pre) => (c >= 1)) &&
((1 < k@pre) => (c <= k)) &&
((!(1 < k@pre)) => ((c == 1)&&(y == z@pre)&&(x == 1)&&(k == k@pre)&&(z == z@pre))) &&
(k == k@pre) &&
(z == z@pre
          loop assigns c, x, y)
    */
    
            while (c < k){
 c = c + 1;
 x = x*z + 1;
 y = y*z;
  }


}