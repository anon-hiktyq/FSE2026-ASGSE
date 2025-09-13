
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct TAG_DSS_DATA
{
 	int stateFlag_A;
 	int stateFlag_B;

}SDSSData;
typedef struct __SwitchSS
{
    int         flgSP;
	SDSSData	mDSSData;
    
} SwitchSS;


void SwitchSSFun(SwitchSS *pIp)

/*@
With pIp_flgSP pIp_mDSSData_stateFlag_A pIp_mDSSData_stateFlag_B
Require pIp->flgSP == pIp_flgSP && pIp->mDSSData.stateFlag_A == pIp_mDSSData_stateFlag_A && pIp->mDSSData.stateFlag_B == pIp_mDSSData_stateFlag_B
Ensure (pIp_mDSSData_stateFlag_A != 1 && pIp_flgSP == 51 && (pIp->flgSP == pIp_flgSP) * (pIp->mDSSData.stateFlag_A == 1) * (pIp->mDSSData.stateFlag_B == 1)) || (pIp_mDSSData_stateFlag_A == 1 && pIp_flgSP == 51 && (pIp->flgSP == pIp_flgSP) * (pIp->mDSSData.stateFlag_A == 0) * (pIp->mDSSData.stateFlag_B == 1)) || (pIp_flgSP != 51 && (pIp->flgSP == pIp_flgSP) * (pIp->mDSSData.stateFlag_A == 0) * (pIp->mDSSData.stateFlag_B == 0))
*/
{
    if (pIp -> flgSP == 0x33){

        if (pIp -> mDSSData.stateFlag_A == 1)
        {

            pIp -> mDSSData.stateFlag_A = 0;
            
        }
        else
        {
            pIp -> mDSSData.stateFlag_A = 1;
        }

        pIp -> mDSSData.stateFlag_B = 1;
    }
    else {

        pIp -> mDSSData.stateFlag_A = 0;

        pIp -> mDSSData.stateFlag_B = 0;
    }

    return;
}
void main11(SwitchSS *pIp)

/*@
With pIp_flgSP pIp_mDSSData_stateFlag_A pIp_mDSSData_stateFlag_B
Require pIp->flgSP == pIp_flgSP && pIp->mDSSData.stateFlag_A == pIp_mDSSData_stateFlag_A && pIp->mDSSData.stateFlag_B == pIp_mDSSData_stateFlag_B
Ensure (0 != 1 && 51 == 51 && pIp->mDSSData.stateFlag_A == 1 && pIp->mDSSData.stateFlag_B == 1 && pIp->flgSP == 51)
*/
{

	pIp -> flgSP = 0x33;
	pIp -> mDSSData.stateFlag_A = 0;
    pIp -> mDSSData.stateFlag_B = 0;

	SwitchSSFun(pIp);

    
    

}