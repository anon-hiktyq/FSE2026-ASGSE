
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


int areElementsEven(int *a, int n) /*@
With a_l
Require store_int_array(a, n, a_l) && n > 0 && n < 100
Ensure Results(__return)
*/
{
    int p = 0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  a_l,    
    store_int_array(a, n, a_l) && n > 0 && n < 100 &&
    ((0 < n@pre) => (0 <= p && p <= n@pre)) &&
((!(0 < n@pre)) => ((p == 0)&&(n == n@pre)&&(a == a@pre))) &&
(n == n@pre) &&
(a == a@pre) &&
(forall (i:Z), 0 <= i && i < p => a_l[i] % 2 == 0
            loop assigns p)
    */
    
            while (p < n) {
        if (a[p]%2 != 0) {
            return 0;
        }
        p = p + 1;
    }
    return 1;
}
void goo25() 
/*@

Require emp

Ensure emp
*/{
    int arr[] = {2,4,6,8,10};
    int res = areElementsEven(arr, 5);
    
}