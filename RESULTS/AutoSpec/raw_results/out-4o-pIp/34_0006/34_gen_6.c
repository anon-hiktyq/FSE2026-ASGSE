
typedef struct __Delay
{

	int			delaytime;

} Delay;


/*@
requires \valid(pIp);
requires pIp->delaytime >= 0;
ensures \forall integer i; 0 <= i <= pIp->delaytime ==> i >= 0;
assigns \nothing;
*/
void DelayFun(Delay* pIp)
{

    int t=0;

    /*@
    loop invariant \forall integer k; 0 <= k < t ==> t >= 0;
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
