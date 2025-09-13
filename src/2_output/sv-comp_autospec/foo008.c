
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void foo008(int a, int b) 

            /*@
            Require a < 1000000 && 0 <= b && b <= 1000000
            Ensure Results(__return)
            */
            {

    int res, cnt;
    res = a;
    cnt = b;
    

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((b@pre > 0) => (res == a + (b@pre - cnt))) &&
((b@pre > 0) => (0 <= cnt && cnt <= b@pre)) &&
((!(b@pre > 0)) => ((cnt == b@pre)&&(res == a@pre)&&(b == b@pre)&&(a == a@pre))) &&
(b == b@pre) &&
(a == a@pre
          loop assigns cnt, res)
    */
    
            while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    
    

}