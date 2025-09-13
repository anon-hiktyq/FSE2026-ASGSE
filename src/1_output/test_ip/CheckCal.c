
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
Ensure emp
*/{

	int i = 0;
	int chksum = 0;

	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp->tcaData[i];
	}

	pIp->chksum = chksum;

	return;
}