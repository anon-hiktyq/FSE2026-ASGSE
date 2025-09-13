
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
    
for (; i < 5; i++) {
    sum -= arr[i];
}
        
return sum;
}