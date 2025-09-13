
typedef struct __Delay
{

	int			delaytime;

} Delay;


void DelayFun(Delay* pIp)
{

    int t=0;

    /*@
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
