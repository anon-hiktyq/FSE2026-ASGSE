

typedef struct __ModPNHP
{

	int		x;
	int	 halfperiod;
	int 	npp2;
	int*	ret;

} ModPNHP;


/*@
requires \valid(pIp);
requires \valid(pIp->ret);
ensures *(pIp->ret) == pIp->x - 2 * pIp->halfperiod;
ensures pIp->npp2 == pIp->x - 2 * pIp->halfperiod;
assigns pIp->npp2;
assigns *(pIp->ret);
*/
void ModPNHPFun(ModPNHP *pIp)
{

    int period;

    period = 2 * pIp -> halfperiod;

    pIp -> npp2 = pIp -> x - period ;

    *(pIp -> ret) = pIp -> npp2;

}


void main19(ModPNHP *pIp)
{

	pIp -> x = 100;
	pIp -> halfperiod = 50;

    ModPNHPFun(pIp);

    // @ assert pIp -> npp2 == 0;

}