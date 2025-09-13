
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __SendUartData
{
/* 输入端口 */
	int		addr[10];
	int		data[10];
    int         len;
	
} SendUartData;

void SendUartDataFun(SendUartData *pIp)

/*@
With pIp_addr_l pIp_data_l pIp_len
Require store_int_array(pIp->addr,10, pIp_addr_l) && store_int_array(pIp->data,10, pIp_data_l) && pIp->len == pIp_len
Ensure emp
*/{
    
	int i =0;

	for (; i < pIp -> len; i++)
	{
		pIp -> addr[i] =  pIp -> data[i];
	}
	return;
}