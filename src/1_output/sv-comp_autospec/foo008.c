
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
    

    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    
    

}