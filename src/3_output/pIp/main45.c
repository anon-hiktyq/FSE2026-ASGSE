typedef struct __SendUartData
{
/* 输入端口 */
	int		addr[10];
	int		data[10];
    int         len;
	
} SendUartData;


typedef struct __SendUartData
{
    /* 输入端口 */
    int addr[10];
    int data[10];
    int len;
} SendUartData;

/*@
    predicate array_copied{L}(SendUartData *p, integer n) =
        \forall integer k; 0 <= k < n ==> p->addr[k] == p->data[k];
*/

/*@
    requires \valid(pIp);
    requires 0 <= pIp->len <= 10;
    requires \valid(pIp->addr + (0 .. 9));
    requires \valid(pIp->data + (0 .. 9));
    ensures \forall integer k; 0 <= k < pIp->len ==> pIp->addr[k] == pIp->data[k];
    ensures \forall integer k; pIp->len <= k < 10 ==> pIp->addr[k] == \at(pIp->addr[k], Pre);
    assigns pIp->addr[0 .. 9];
*/
void SendUartDataFun(SendUartData *pIp)
{
    int i = 0;

    /*@
        loop invariant 0 <= i <= pIp->len;
        loop invariant \forall integer k; 0 <= k < i ==> pIp->addr[k] == pIp->data[k];
        loop invariant \forall integer k; i <= k < 10 ==> pIp->addr[k] == \at(pIp->addr[k], Pre);
        loop assigns i, pIp->addr[0 .. pIp->len - 1];
        loop variant pIp->len - i;
    */
    for (; i < pIp->len; i++)
    {
        pIp->addr[i] = pIp->data[i];
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

    /*@ assert pIp->addr[0] == pIp->data[0]; */
    /*@ assert pIp->addr[1] == pIp->data[1]; */
    /*@ assert pIp->addr[2] == pIp->data[2]; */
   
}