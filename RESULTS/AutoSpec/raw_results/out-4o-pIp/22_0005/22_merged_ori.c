

typedef struct __ModPNHP
{

	int		x;
	int	 halfperiod;
	int 	npp2;
	int*	ret;

} ModPNHP;


/*@
requires pIp->halfperiod >= 0;
requires \valid(pIp- > ret);
requires \valid(pIp);
requires \valid(pIp) && \valid(pIp- > ret);
requires \separated(pIp, pIp- > ret);
ensures pIp- > npp2 == pIp- > x - 2 * pIp- > halfperiod;
ensures pIp- > npp2 == pIp- > x - (2 * pIp- > halfperiod);
ensures *(pIp- > ret) == pIp- > npp2;
assigns pIp- > npp2, *(pIp- > ret);
*/
void ModPNHPFun(ModPNHP *pIp)
{

    int period;

    period = 2 * pIp -> halfperiod;

    pIp -> npp2 = pIp -> x - period ;

    *(pIp -> ret) = pIp -> npp2;

}


void main22(ModPNHP *pIp)
{

	pIp -> x = 100;
	pIp -> halfperiod = 50;

    ModPNHPFun(pIp);

    // @ assert pIp -> npp2 == 0;
    // @ assert *(pIp -> ret) == 0;
    // @ assert pIp -> x == 100;
    // @ assert pIp -> halfperiod == 50;
}