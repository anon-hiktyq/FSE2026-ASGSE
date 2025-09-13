
typedef struct __Delay
{
    /* 输入端口 */
	int			delaytime;
	/* 输出端口 */
	/* 输入输出端口 */
	/* 状态变量 */
	/* 参数变量 */
} Delay;


void DelayFun(Delay* pIp)
{

    int t=0;

    /*@
    loop invariant t <= pIp->delaytime;
    loop invariant 0 <= t <= pIp->delaytime;
    loop invariant pIp->delaytime >= 0 ==> t >= 0;
    loop invariant pIp->delaytime < 0 ==> t == 0;
    loop invariant t == \at(t, Pre) + t;
    loop invariant 0 <= t;
    loop assigns t;
    */
    for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    // @ assert pIp->delaytime >= 0 ==> t == pIp -> delaytime;

    return ;
}


void main33(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    // @ assert pIp -> delaytime == 10;
}