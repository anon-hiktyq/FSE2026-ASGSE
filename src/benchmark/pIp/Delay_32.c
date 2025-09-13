
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
requires \valid(pIp) && pIp->delaytime >= 0;
*/
void DelayFun(Delay* pIp)
{

    int t=0;

    for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    /*@ assert t == pIp -> delaytime; */

    return ;
}

/*@
requires \valid(pIp);
*/
void main32(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}