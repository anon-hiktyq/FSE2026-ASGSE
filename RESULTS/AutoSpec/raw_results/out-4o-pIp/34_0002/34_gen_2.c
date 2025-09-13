
typedef struct __Delay
{

	int			delaytime;

} Delay;


/*@
requires \valid(pIp);
requires pIp->delaytime >= 0;
assigns \nothing;
ensures \forall integer t; 0 <= t < pIp->delaytime ==> t >= 0;
ensures pIp->delaytime == \old(pIp->delaytime);
*/
void DelayFun(Delay* pIp)
{

    int t=0;

    /*@
    loop invariant 0 <= t;
    loop assigns t;
    */
    for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    // @ assert t >= 0;

    return ;
}

void main34(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    // @ assert pIp -> delaytime == 10;
}
