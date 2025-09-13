
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main30(int x,int y,int n) 

            /*@
            Require emp
            Ensure Results(__return)
            */
            {
    // variable declarations
	int z=0;
	int w=0;
	int p=0;

    //precondition
    // loop body

 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((n@pre > 0) => (z == (n@pre - n) * (x * x))) &&
((n@pre > 0) => (w == (n@pre - n) * (y * y))) &&
((n@pre > 0) => (p == (n@pre - n) * (x * y))) &&
((!(n@pre > 0)) => ((p == 0)&&(w == 0)&&(z == 0)&&(n == n@pre)&&(y == y@pre)&&(x == x@pre))) &&
(y == y@pre) &&
(x == x@pre
      loop assigns z, w, p, n)
    */
    
    while(n > 0) {
        z = z + x * x;
        w = w + y * y;
        p = p + x * y;
        n -= 1;
    }
    // post-condition
	
}