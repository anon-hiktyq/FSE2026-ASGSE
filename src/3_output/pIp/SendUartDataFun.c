
typedef struct __SendUartData
{
/* 输入端口 */
	int		addr[10];
	int		data[10];
    int         len;
	
} SendUartData;

        /*@
        predicate copied_data{L}(SendUartData *pIp, integer n) =
            \forall integer j; 0 <= j < n ==> pIp->addr[j] == pIp->data[j];
        predicate unchanged_data{L1,L2}(SendUartData *pIp) = 
            \forall integer j; 0 <= j < 10 ==> \at(pIp->data[j],L1) == \at(pIp->data[j],L2);
        */
        
/*@
    requires \valid(pIp);
requires 0 <= pIp->len <=10;
    */
    
void SendUartDataFun(SendUartData *pIp)
{
    
	int i =0;

	
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (!(0 < \at(pIp,Pre) -> len)) ==> ((i == 0)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->len == \at(pIp->len,Pre)));
          loop invariant pIp == \at(pIp,Pre);
          loop invariant \at(pIp,Pre)->len == \at(pIp->len,Pre);
          loop invariant unchanged_data{Here,Pre}(pIp);
          loop invariant \valid(pIp->addr + (0 .. 9));
          loop invariant \forall integer j; 0 <= j < i ==> pIp->addr[j] == pIp->data[j];
          loop assigns i, pIp->addr[0 .. 9];
            */
            for (; i < pIp -> len; i++)
	{
		pIp -> addr[i] =  pIp -> data[i];
	}
            
	return;
}
