

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
	loop invariant len < pIp-;
	loop invariant i <= pIp-;
	loop invariant \forall integer k; 0 <= k < i ==> pIp->addr[k] == pIp->data[k];
	loop invariant \forall integer j; 0 <= j < i ==> pIp->addr[j] == pIp->data[j];
	loop invariant 0 <= i;
	loop assigns pIp->addr[0..pIp->len-1];
	loop assigns pIp->addr[0 .. pIp->len-1];
	loop assigns i;
	```c;
	```;
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
main45(SendUartData *pIp)
{
   
    pIp->len = 3;
    SendUartDataFun(pIp);

    // @ assert pIp->addr[0] == pIp->data[0];
    // @ assert pIp->addr[1] == pIp->data[1];
    // @ assert pIp->addr[2] == pIp->data[2];
   
}