
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main12(int A,int B)

            /*@
            Require A >= 0 && B >= 1
            Ensure Results(__return)
            */
            {
    
   
    int q = 0;
    int r = 0;
    int t = A;
   
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((A@pre != 0) => (q * B + r + t == A)) &&
((A@pre != 0) => (((t == A@pre) && (r == 0) && (q == 0) && (B == B@pre) && (A == A@pre)) || (0 <= r && r < B))) &&
((A@pre != 0) => (0 <= t && t <= A@pre)) &&
((!(A@pre != 0)) => ((t == A@pre) && (r == 0) && (q == 0) && (B == B@pre) && (A == A@pre))) &&
(B == B@pre) &&
(A == A@pre
        loop assigns q, r, t)
    */
    
    while(t != 0) {
        if (r + 1 == B) {
            q = q + 1;
            r = 0;
            t = t - 1;
        }
        else {
            r = r + 1;
            t = t - 1;
        }
    }
    
}