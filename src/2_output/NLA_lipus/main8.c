
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main8(int x,int y)

            /*@
            Require x >= 1 && y >= 1
            Ensure Results(__return)
            */
            {
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (a >= 0 && b >= 0
              loop assigns a, b, p, q, r, s)
    */
    
            while(a!=b){
      if (a>b) {
         a = a-b;
         p = p-q;
         r = r-s;
      }
      else {
         b = b-a;
         q = q-p;
         s = s-r;
      }
  }
 
  
}