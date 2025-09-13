
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __CheckCal
{

	int		len;
	int		pkv[10];
	int     chksum;
	
} CheckCal;

void CheckCalFun(CheckCal *pIp)

/*@
With pIp_len pIp_pkv_l pIp_chksum
Require pIp->len == pIp_len && store_int_array(pIp->pkv,10, pIp_pkv_l) && pIp->chksum == pIp_chksum
Ensure emp
*/{

	int i = 0;
	int chksum = 0;

	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	pIp->chksum = chksum;


	return;
}