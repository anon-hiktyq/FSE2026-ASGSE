
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int sumArray(int arr[5]) 
/*@
With arr_l
Require store_int_array(arr,5, arr_l)
Ensure Results(__return)
*/{
    int sum = 0;
   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  arr_l,    
    store_int_array(arr, 5, arr_l) &&
    (0 <= i && i <= 5 ) &&
((i < 5) => (sum == sum(arr, 0, i)) ) &&
((!(i < 5)) => (sum == sum(arr, 0, i)) ) &&
(arr == arr@pre)
    */
    
        for (int i = 0; i < 5; i++) {
    sum += arr[i];
}
    return sum;
}