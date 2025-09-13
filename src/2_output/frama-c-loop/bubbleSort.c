
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

void bubbleSort(int *a, int n) 
/*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure (n - 1 <= 0 && n > 0 && n > 0 && n < 100 && store_int_array(a, n, a_l))
*/
{
    if (n <= 0) return;
    int i, j, temp;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for(i=n-1; i>0; i--) {
       
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 for(j=0; j<i; j++) {
            if (a[j] > a[j+1]) {
                temp = a[j];
                a[j] = a[j+1];
                a[j+1] = temp;
            }
        }
    }
}