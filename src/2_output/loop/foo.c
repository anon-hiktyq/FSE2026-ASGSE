
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    

void foo()
/*@

Require emp
Ensure (exists y_53 x_52, y_53 >= 100000 && 0 <= y_53 && y_53 <= 100000 && x_52 == 1 + y_53 * (y_53 - 1) / 2)
*/
{
  
    int x = 1;
    int y = 0;
    
    
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= y && y <= 100000 ) &&
(x == 1 + y * (y - 1) / 2 )
    */
    
            while (y < 100000) {
      
       x  = x + y;
       y  = y + 1;
      
  
    }
  
    
  }