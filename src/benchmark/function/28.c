
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
    
    /*@ assert t >= 0; */

    return ;
}

/*@
requires \valid(pIp);
*/
void goo28(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}
