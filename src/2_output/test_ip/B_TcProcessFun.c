
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    typedef struct __B_TcProcess
{

	int			tcaData[3];
	int         chksum;
	int 		len;
	int     	flgMode;

} B_TcProcess;


void CheckCal(B_TcProcess *pIp)
/*@
With pIp_tcaData_l pIp_tcaData_0 pIp_tcaData_1 pIp_tcaData_2 pIp_chksum pIp_len pIp_flgMode
Require store_int_array(pIp->tcaData,3, pIp_tcaData_l) && pIp_tcaData_l[0] == pIp_tcaData_0 && pIp_tcaData_l[1] == pIp_tcaData_1 && pIp_tcaData_l[2] == pIp_tcaData_2 && pIp->chksum == pIp_chksum && pIp->len == pIp_len && pIp->flgMode == pIp_flgMode
Ensure (0 >= pIp_len && pIp_tcaData_l[0] == pIp_tcaData_0 && pIp_tcaData_l[1] == pIp_tcaData_1 && pIp_tcaData_l[2] == pIp_tcaData_2 && store_int_array(&pIp->tcaData, 3, pIp_tcaData_l) * (pIp->chksum == 0) * (pIp->len == pIp_len) * (pIp->flgMode == pIp_flgMode))
*/
{

	int i = 0;
	int chksum = 0;


 	/*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp->tcaData[i];
	}

	pIp->chksum = chksum;

	return;
}
void B_TcProcessFun(B_TcProcess *pIp)

/*@
With pIp_tcaData_l pIp_tcaData_0 pIp_tcaData_1 pIp_tcaData_2 pIp_chksum pIp_len pIp_flgMode
Require store_int_array(pIp->tcaData,3, pIp_tcaData_l) && pIp_tcaData_l[0] == pIp_tcaData_0 && pIp_tcaData_l[1] == pIp_tcaData_1 && pIp_tcaData_l[2] == pIp_tcaData_2 && pIp->chksum == pIp_chksum && pIp->len == pIp_len && pIp->flgMode == pIp_flgMode
Ensure emp
*/{

	int chksum;
	unint08 i;

	if ((pIp -> tcaData[0] == 0xE1) && (pIp -> tcaData[1] == 0x00))
	{

		CheckCal(pIp);

	    if(pIp -> tcaData[3] == chksum)
	    {

	    	if(pIp -> tcaData[2] == 0)
	    	{
	    		pIp->flgMode = 0x00 ;
	    	}
	    	else if(pIp -> tcaData[2] == 1)
	    	{
	    		pIp->flgMode = 0x33 ;
	    	}
	    	else
	    	{
	    		pIp->flgMode = 0x44 ;
	    	}
	    }
	}

	return;
}