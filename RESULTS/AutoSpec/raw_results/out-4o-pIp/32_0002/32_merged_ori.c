
typedef struct __Delay
{
    /* 输入端口 */
	int			delaytime;
	/* 输出端口 */
	/* 输入输出端口 */
	/* 状态变量 */
	/* 参数变量 */
} Delay;

/*@
requires pIp->delaytime >= 0;
requires \valid(pIp);
ensures pIp->delaytime >= 0;
ensures pIp- > delaytime == \old(pIp- > delaytime);
ensures \result == \nothing;
ensures \forall integer t; 0 <= t < pIp->delaytime ==> t >= 0;
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
    
    // @ assert t == pIp -> delaytime;

    return ;
}


void main32(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    // @ assert pIp -> delaytime == 10;
}