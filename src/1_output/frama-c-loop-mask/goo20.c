
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int sumArray(int *a, int n) /*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure Results(__return)
*/
{
    int p = 0, sum = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 while (p < n) {
        sum = sum + a[p];
        p++;
    }
    return sum;
}
void goo20() 
/*@

Require emp

Ensure emp
*/{
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = sumArray(arr, 5);
}