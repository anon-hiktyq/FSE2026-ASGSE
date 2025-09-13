
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

void CheckCal(CheckCal *pIp)

/*@
With pIp_len pIp_pkv_v pIp_pkv pIp_chksum
Require pIp->len == pIp_len && *(pIp->pkv) == pIp_pkv_v && (pIp->pkv) == pIp_pkv && pIp->chksum == pIp_chksum
Ensure emp
*/{

	int i = 0;
	int chksum = 0;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= i && i <= pIp->len) &&
(chksum == sum(pIp->pkv, 0, i)) &&
(\valid(pIp)) &&
(\valid(pIp->pkv + (0..9))) &&
(pIp->len <= 10) &&
(forall (j:Z), 0 <= j && j < 10 => 0 <= pIp->pkv_l[j] && pIp->pkv_l[j] <= 100) &&
(forall (k:Z), i <= k && k < pIp->len => chksum == sum(pIp->pkv, 0, i)
        loop assigns i, chksum
        loop variant pIp->len - i)
    */
    
    for (; i < pIp->len; i++)
    {
        chksum = chksum + pIp->pkv[i];
    }

	
	
	


	pIp->chksum = chksum;


	return;
}