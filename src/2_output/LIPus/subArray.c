
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int subArray(int arr[5]) 

/*@
With arr_l
Require store_int_array(arr,5, arr_l)
Ensure Results(__return)
*/{
    int sum = 0;  
    int i =0; 
    
 
/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  arr_l,    
    store_int_array(arr, 5, arr_l) &&
    (\valid(arr+(0..4)) ) &&
(sum == -sum(arr, 0, i) ) &&
(0 <= i && i <= 5 ) &&
(arr == arr@pre)
    */
    
            for (; i < 5; i++) {
    sum -= arr[i];
}
        
return sum;
}