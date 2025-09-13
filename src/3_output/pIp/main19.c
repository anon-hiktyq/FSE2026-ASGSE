

typedef struct __ModPNHP
{

	int		x;
	int	 halfperiod;
	int 	npp2;
	int*	ret;

} ModPNHP;

/*@
requires \valid(pIp) && \valid(pIp->ret);
	requires \separated(pIp,pIp->ret);

ensures pIp->x == \old(pIp->x)&&pIp->halfperiod == \old(pIp->halfperiod)&&pIp->npp2 == \old(pIp->x) - 2 * \old(pIp->halfperiod)&&pIp->ret == \old(pIp->ret)&&*\old(pIp->ret) == \old(pIp->x) - 2 * \old(pIp->halfperiod);

*/

void ModPNHPFun(ModPNHP *pIp)

{

    int period;

    period = 2 * pIp -> halfperiod;

    pIp -> npp2 = pIp -> x - period ;

    *(pIp -> ret) = pIp -> npp2;

}/*@
    requires \valid(pIp) && \valid(pIp->ret);
	requires \separated(pIp,pIp->ret);
    */
    
void main19(ModPNHP *pIp)
{

	pIp -> x = 100;
	pIp -> halfperiod = 50;

    ModPNHPFun(pIp);

    /*@ assert pIp -> npp2 == 0; */

}