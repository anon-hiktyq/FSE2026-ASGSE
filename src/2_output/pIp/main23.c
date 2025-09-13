
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __CheckCal
{

	int		len;
	int		*pkv;
	int     chksum;
	
} CheckCal;

void main23(CheckCal *pIp)

/*@
With pIp_len pIp_pkv_v pIp_pkv pIp_chksum
Require pIp->len == pIp_len && *(pIp->pkv) == pIp_pkv_v && (pIp->pkv) == pIp_pkv && pIp->chksum == pIp_chksum
Ensure emp
*/{

	int i = 0;
	int chksum = 0;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < pIp@pre->len) => (0 <= i && i <= pIp@pre->len)) &&
((0 < pIp@pre->len) => (chksum == sum(pIp->pkv, 0, i))) &&
(!(0 < pIp@pre->len) => ((chksum == 0) && (i == 0) && (pIp == pIp@pre) && (pIp@pre->len == pIp->len@pre) && (pIp@pre->pkv == pIp->pkv@pre) && (*pIp->pkv@pre == *pIp->pkv@pre) && (pIp@pre->chksum == pIp->chksum@pre))) &&
(pIp == pIp@pre) &&
(pIp@pre->len == pIp->len@pre) &&
(pIp@pre->pkv == pIp->pkv@pre) &&
(*pIp->pkv@pre == *pIp->pkv@pre) &&
(pIp@pre->chksum == pIp->chksum@pre) &&
(valid_pkvs(pIp)
      loop assigns chksum, i)
    */
    
    for(; i < pIp->len; i++)
	{
	    chksum = chksum + pIp->pkv[i];
	}

	
	
	


	pIp->chksum = chksum;


	return;
}