
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __ModPNHP
{

	int		x;
	int	 halfperiod;
	int 	npp2;
	int*	ret;

} ModPNHP;


void ModPNHPFun(ModPNHP *pIp)
/*@
With pIp_x pIp_halfperiod pIp_npp2 pIp_ret_v pIp_ret
Require pIp->x == pIp_x && pIp->halfperiod == pIp_halfperiod && pIp->npp2 == pIp_npp2 && *(pIp->ret) == pIp_ret_v && (pIp->ret) == pIp_ret
Ensure ((pIp->x == pIp_x) * (pIp->halfperiod == pIp_halfperiod) * (pIp->npp2 == pIp_x - 2 * pIp_halfperiod) * (pIp->ret == pIp_ret) * (*pIp_ret == pIp_x - 2 * pIp_halfperiod))
*/
{

    int period;

    period = 2 * pIp -> halfperiod;

    pIp -> npp2 = pIp -> x - period ;

    *(pIp -> ret) = pIp -> npp2;

}
void main19(ModPNHP *pIp)

/*@
With pIp_x pIp_halfperiod pIp_npp2 pIp_ret_v pIp_ret
Require pIp->x == pIp_x && pIp->halfperiod == pIp_halfperiod && pIp->npp2 == pIp_npp2 && *(pIp->ret) == pIp_ret_v && (pIp->ret) == pIp_ret
Ensure emp
*/{

	pIp -> x = 100;
	pIp -> halfperiod = 50;

    ModPNHPFun(pIp);

    

}