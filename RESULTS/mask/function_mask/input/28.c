
typedef struct __Delay
{

	int			delaytime;

} Delay;

/*@
requires \valid(pIp);
requires 0 <= pIp->delaytime <= 10;
*/
void DelayFun(Delay* pIp)
{

    int t=0;

    for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    /* MASK_ACSL_ASSERT */

    return ;
}

/*@
requires \valid(pIp);
*/
void goo28(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    /* MASK_ACSL_ASSERT */
}
