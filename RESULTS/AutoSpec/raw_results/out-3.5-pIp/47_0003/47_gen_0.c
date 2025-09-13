

typedef struct __SendUartData
{
/* 输入端口 */
	int		addr[10];
	int		data[10];
    int         len;
	
} SendUartData;


/*@
requires \valid(pIp);
requires 0 <= pIp->len <=10;
*/
void SendUartDataFun(SendUartData *pIp)
{
	int i =0;

	/*@
	loop invariant 0 <= i <= pIp->len;
	loop invariant \forall integer k; 0 <= k < i ==> pIp->addr[k] == pIp->data[k];
	loop assigns i;
	loop assigns pIp->addr[0..9];
	*/
	for (; i < pIp -> len; i++)
	{
		pIp -> addr[i] =  pIp -> data[i];
	}
	return;
}

/*@
requires \valid(pIp);
requires 0 <= pIp->len <=10;
*/
main47(SendUartData *pIp)
{
    
    pIp->len = 3;
    SendUartDataFun(pIp);

    // @ assert pIp->addr[3] == pIp->addr[3];
    // @ assert pIp->addr[4] == pIp->addr[4];
    // @ assert pIp->addr[5] == pIp->addr[5];
    
}