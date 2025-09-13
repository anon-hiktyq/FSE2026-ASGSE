
typedef struct __Delay
{

	int			delaytime;

} Delay;


/*@
requires pIp->delaytime >= 0;
requires \valid(pIp);
ensures pIp->delaytime >= 0;
ensures pIp- > delaytime == \old(pIp- > delaytime);
ensures \unchanged(pIp- > delaytime);
ensures \result == \nothing;
ensures \nothing;
ensures \forall integer t; t >= 0 ==> t < pIp->delaytime;
ensures \forall integer t; 0 <= t < pIp->delaytime ==> t < pIp->delaytime;
ensures \forall integer k; 0 <= k < pIp->delaytime ==> k < pIp->delaytime;
assigns \nothing;
*/
void DelayFun(Delay* pIp)
{

    int t=0;

    /*@
    loop invariant \forall integer k; 0 <= k < t ==> k < pIp->delaytime;
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
