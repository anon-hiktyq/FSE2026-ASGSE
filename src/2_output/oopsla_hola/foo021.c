
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo021(int n,int j,int v) 

            /*@
            Require n > 0 && n < 10
            Ensure Results(__return)
            */
            {
  int c1 = 4000;
  int c2 = 2000;
  int i = 0;
  int k = 0;
 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < n@pre) => (((k == 0)&&(i == 0)&&(c2 == 2000)&&(c1 == 4000)&&(v == v@pre)&&(j == j@pre)&&(n == n@pre)) || (v == 0 => k == 4000 * i + 2000 * (n@pre - i)) || (v == 1 => k == 2000 * i + 4000 * (n@pre - i)))) &&
((0 < n@pre) => (0 <= i && i <= n)) &&
((0 < n@pre) => (k >= 2000 * i)) &&
((0 < n@pre) => (k <= 4000 * i)) &&
((!(0 < n@pre)) => ((k == 0)&&(i == 0)&&(c2 == 2000)&&(c1 == 4000)&&(v == v@pre)&&(j == j@pre)&&(n == n@pre))) &&
(c2 == 2000) &&
(c1 == 4000) &&
(j == j@pre) &&
(n == n@pre
          loop assigns i, k, v)
    */
    
            while( i < n ) {
    i++;
    if(unknown() % 2 == 0) {
        v = 0;
    }
    else v = 1;
    
    if( v == 0 ){
      k += c1;
    }else {
      k += c2;
    }
  }
  
  
}