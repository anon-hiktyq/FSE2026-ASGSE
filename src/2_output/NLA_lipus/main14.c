
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int main14(int a,int b)

            /*@
            Require a >= 0 && b >= 0
            Ensure Results(__return)
            */
            {
   
    int x=a;
    int y=b;
    int z=0;

    // loop body
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((b@pre != 0) => (y >= 0 && y <= b@pre)) &&
((b@pre != 0) => (z + y * x == a * b)) &&
((!(b@pre != 0) ) => ((z == 0) && (y == b@pre) && (x == a@pre) && (b == b@pre) && (a == a@pre))) &&
(b == b@pre) &&
(a == a@pre
      loop assigns z, x, y)
    */
    
    while (y != 0) {
        if (y % 2 == 1) {
            z = z + x;
            y = y - 1;
        }
        x = 2 * x;
        y = y / 2;
    }

    
}