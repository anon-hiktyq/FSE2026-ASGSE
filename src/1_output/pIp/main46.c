
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
Ensure (0 >= pIp_len && store_int_array(&pIp->addr, 10, pIp_addr_l) * store_int_array(&pIp->data, 10, pIp_data_l) * (pIp->len == pIp_len))
*/
{
    
	int i =0;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (; i < pIp -> len; i++)
	{
		pIp -> addr[i] =  pIp -> data[i];
	}
	return;
}
main46(SendUartData *pIp)

/*@
With pIp_addr_l pIp_data_l pIp_len
Require store_int_array(pIp->addr,10, pIp_addr_l) && store_int_array(pIp->data,10, pIp_data_l) && pIp->len == pIp_len
Ensure Results(__return)
*/{
    
    pIp->len = 5;
    pIp->data[0] = 1;
    pIp->data[1] = 2;
    pIp->data[2] = 3;
    pIp->data[3] = 4;
    pIp->data[4] = 5;
    SendUartDataFun(pIp);
    
    
    
    
    
    

}