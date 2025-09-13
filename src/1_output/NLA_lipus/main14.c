
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
    while(y!=0) {
     
     if (y%2 ==1 ){
          z = z+x;
          y = y-1;
     }
     x = 2*x;
     y = y/2;
    }

    
}