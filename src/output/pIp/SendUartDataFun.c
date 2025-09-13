
typedef struct __SendUartData
{
    /* 输入端口 */
    int addr[10];
    int data[10];
    int len;

} SendUartData;

/*@
    predicate copied_data{L}(SendUartData *pIp, integer n) =
        \forall integer j; 0 <= j < n ==> pIp->addr[j] == pIp->data[j];
    predicate unchanged_data{L1,L2}(SendUartData *pIp) = 
        \forall integer j; 0 <= j < 10 ==> \at(pIp->data[j],L1) == \at(pIp->data[j],L2);
*/

/*@
    requires \valid(pIp);
    requires 0 <= pIp->len <= 10;
    ensures copied_data{Post}(pIp, pIp->len);
    ensures \forall integer j; pIp->len <= j < 10 ==> pIp->addr[j] == \at(pIp->addr[j],Pre);
    assigns pIp->addr[0 .. pIp->len - 1];
*/
void SendUartDataFun(SendUartData *pIp)
{
    int i = 0;

    /*@
        loop invariant 0 <= i <= pIp->len;
        loop invariant \forall integer j; 0 <= j < i ==> pIp->addr[j] == pIp->data[j];
        loop invariant \forall integer j; i <= j < 10 ==> pIp->addr[j] == \at(pIp->addr[j],Pre);
        loop invariant unchanged_data{Here,Pre}(pIp);
        loop invariant \valid(pIp->addr + (0 .. 9));
        loop assigns i, pIp->addr[0 .. 9];
        loop variant pIp->len - i;
    */
    for (; i < pIp->len; i++)
    {
        pIp->addr[i] = pIp->data[i];
    }

    return;
}
