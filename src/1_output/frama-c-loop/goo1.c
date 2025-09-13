
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int arraymax(int* a, int n) /*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure Results(__return)
*/
{
  int i = 1;
  int max = a[0];

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, n, a_l) && n > 0 && n < 100 &&
    (forall (j:Z), 0 <= j && j < i => a_l[j] <= max // All processed elements are less than or equal to max
              loop variant n - i // Ensure the loop will terminate)
    */
    
            while (i < n) {
    if (max < a[i])
    max = a[i];
    i = i + 1;
  }
  return max;
}
void goo1() 
/*@

Require emp

Ensure emp
*/{
  int arr[5] = {1, 2, 3, 4, 5};
  int max = arraymax(arr, 5);
  
  
  
  
  
}