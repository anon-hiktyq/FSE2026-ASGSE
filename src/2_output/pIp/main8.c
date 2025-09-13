
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct TAG_UPS_2MS
{	
	int flgABChoose;				
    int wPulse;
	int stateFlag[2];				
    
} SThrDistribute;
typedef struct __ThrABAutoChoose
{
	SThrDistribute			mThrDistribute;
	
} ThrABAutoChoose;


void ThrABAutoChooseFun(ThrABAutoChoose *pIp)
/*@
With pIp_mThrDistribute_flgABChoose pIp_mThrDistribute_wPulse pIp_mThrDistribute_stateFlag_l
Require pIp->mThrDistribute.flgABChoose == pIp_mThrDistribute_flgABChoose && pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse && store_int_array(pIp->mThrDistribute.stateFlag,2, pIp_mThrDistribute_stateFlag_l)
Ensure (pIp_mThrDistribute_stateFlag_l[1] == 1 && pIp_mThrDistribute_stateFlag_l[0] == 1 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, pIp_mThrDistribute_stateFlag_l) * (pIp->mThrDistribute.flgABChoose == 204) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (pIp_mThrDistribute_stateFlag_l[1] == 1 && pIp_mThrDistribute_stateFlag_l[0] == 0 && pIp_mThrDistribute_stateFlag_l[0] != 1 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, pIp_mThrDistribute_stateFlag_l) * (pIp->mThrDistribute.flgABChoose == 51) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (pIp_mThrDistribute_stateFlag_l[0] != 0 && pIp_mThrDistribute_stateFlag_l[0] != 1 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, pIp_mThrDistribute_stateFlag_l) * (pIp->mThrDistribute.flgABChoose == 0) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (pIp_mThrDistribute_stateFlag_l[1] != 1 && pIp_mThrDistribute_stateFlag_l[0] == 0 && pIp_mThrDistribute_stateFlag_l[0] != 1 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, pIp_mThrDistribute_stateFlag_l) * (pIp->mThrDistribute.flgABChoose == 0) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (pIp_mThrDistribute_stateFlag_l[0] != 0 && pIp_mThrDistribute_stateFlag_l[1] != 1 && pIp_mThrDistribute_stateFlag_l[0] == 1 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, pIp_mThrDistribute_stateFlag_l) * (pIp->mThrDistribute.flgABChoose == 0) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse))
*/
{

    if ((pIp -> mThrDistribute.stateFlag[0] == 1) &&
        (pIp -> mThrDistribute.stateFlag[1] == 1))
    {

        pIp -> mThrDistribute.flgABChoose = 0xCC ;
    }
    else if ((pIp -> mThrDistribute.stateFlag[0] == 0) &&
             (pIp -> mThrDistribute.stateFlag[1] == 1))
    {
        pIp -> mThrDistribute.flgABChoose = 0x33 ;
    }
    else
    {
        pIp -> mThrDistribute.flgABChoose = 0x00 ;
    }

    return ;
}
void main8(ThrABAutoChoose *pIp)

/*@
With pIp_mThrDistribute_flgABChoose pIp_mThrDistribute_wPulse pIp_mThrDistribute_stateFlag_l
Require pIp->mThrDistribute.flgABChoose == pIp_mThrDistribute_flgABChoose && pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse && store_int_array(pIp->mThrDistribute.stateFlag,2, pIp_mThrDistribute_stateFlag_l)
Ensure (replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] != 0 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[1] != 1 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] == 1 && pIp->mThrDistribute.flgABChoose == 0 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[1] != 1 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] == 0 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] != 1 && pIp->mThrDistribute.flgABChoose == 0 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] != 0 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] != 1 && pIp->mThrDistribute.flgABChoose == 0 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[1] == 1 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] == 0 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] != 1 && pIp->mThrDistribute.flgABChoose == 51 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse)) || (replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[1] == 1 && replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))[0] == 1 && pIp->mThrDistribute.flgABChoose == 204 && store_int_array(&pIp->mThrDistribute.stateFlag, 2, replace_Znth(1, 1, replace_Znth(0, 1, pIp_mThrDistribute_stateFlag_l))) * (pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse))
*/
{

	pIp -> mThrDistribute.stateFlag[0] = 1;
	pIp -> mThrDistribute.stateFlag[1] = 1;
 

	ThrABAutoChooseFun(pIp);
    
     
        
     
      

}