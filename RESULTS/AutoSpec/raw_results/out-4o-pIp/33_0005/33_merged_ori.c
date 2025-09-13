
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
ensures t == pIp- > delaytime;
ensures pIp->delaytime >= 0 ==> \result == pIp->delaytime;
ensures \forall integer t; 0 <= t < pIp->delaytime ==> t < pIp->delaytime;
ensures \forall integer k; 0 <= k < \result ==> k < pIp->delaytime;
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
    
    // @ assert pIp->delaytime >= 0 ==> t == pIp -> delaytime;

    return ;
}


void main33(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    // @ assert pIp -> delaytime == 10;
}