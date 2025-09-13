
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
requires \valid(pIp) ;
*/
void DelayFun(Delay* pIp)
{

    int t=0;

    for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    /* MASK_ACSL_ASSERT */

    return ;
}

/*@
requires \valid(pIp);
*/
void goo27(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    /* MASK_ACSL_ASSERT */
}