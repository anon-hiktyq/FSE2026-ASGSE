
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    


void increment_array_by(int* arr, int n, int c) /*@
With arr_l
Require store_int_array(arr, n, arr_l) && n > 0 && n < 100
Ensure emp
*/
{
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  arr_l,    
    store_int_array(arr, n, arr_l) && n > 0 && n < 100 &&
    ((forall (j:Z), 0 <= j && j < i => arr_l[j] == arr_l[j]@pre + c)) &&
((forall (k:Z), i <= k && k < n => arr_l[k] == arr_l[k]@pre)) &&
(c == c@pre) &&
(n == n@pre) &&
(arr == arr@pre)
    */
    
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}
void main15() 
/*@

Require emp

Ensure emp
*/{
    int arr[5] = {1, 2, 3, 4, 5};
    increment_array_by(arr, 5, 2);
    
    
    
    
    
}