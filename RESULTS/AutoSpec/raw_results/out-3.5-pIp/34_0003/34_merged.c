
typedef struct __Delay
{

	int			delaytime;

} Delay;


/*@
requires pIp->delaytime >= 0;
requires \valid(pIp);
assigns \nothing;
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
    
    //@ assert t >= 0;

    return ;
}

void main34(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    //@ assert pIp -> delaytime == 10;
}
