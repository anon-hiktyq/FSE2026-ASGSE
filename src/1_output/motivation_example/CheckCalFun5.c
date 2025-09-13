
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __CheckCal
{
        int pkv[10];
        int len;
        
} CheckCal;

void CheckCalFun5(CheckCal *pIp)
/*@
With pIp_pkv_l pIp_len
Require store_int_array(pIp->pkv,10, pIp_pkv_l) && pIp->len == pIp_len
Ensure emp
*/{
        int i = 0;
        int chksum = 0;

        for (; i < pIp->len; i++){
            chksum = chksum + pIp->pkv[i];
        }

        return chksum;

}