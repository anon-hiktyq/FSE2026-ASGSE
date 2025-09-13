
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct TAG_FAULT_WARNING
{

    int Wsp;
    int countSPLost;
    int countSPSeen;
    int countSPset;

} SFWarning;
typedef struct TAG_DSS_DATA
{
	int flgSP;
}SDSSData;
typedef struct __SoftFaultJudgeSP
{

 SDSSData mDSSData;
 SFWarning mFWarning;


} SoftFaultJudgeSP;


void SoftFaultJudgeSPFun(SoftFaultJudgeSP *pIp)

/*@
With pIp_mDSSData_flgSP pIp_mFWarning_Wsp pIp_mFWarning_countSPLost pIp_mFWarning_countSPSeen pIp_mFWarning_countSPset
Require pIp->mDSSData.flgSP == pIp_mDSSData_flgSP && pIp->mFWarning.Wsp == pIp_mFWarning_Wsp && pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost && pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen && pIp->mFWarning.countSPset == pIp_mFWarning_countSPset
Ensure (pIp_mFWarning_countSPLost > 33750 && pIp_mFWarning_countSPSeen + 1 <= 2 && pIp_mFWarning_countSPLost != 0 && pIp_mDSSData_flgSP != 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == 235) * (pIp->mFWarning.countSPLost == 0) * (pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen + 1) * (pIp->mFWarning.countSPset == 0)) || (pIp_mFWarning_countSPLost + 1 > 33750 && pIp_mDSSData_flgSP == 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == 235) * (pIp->mFWarning.countSPLost == 0) * (pIp->mFWarning.countSPSeen == 0) * (pIp->mFWarning.countSPset == 0)) || (pIp_mFWarning_countSPLost + 1 <= 33750 && pIp_mDSSData_flgSP == 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == pIp_mFWarning_Wsp) * (pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost + 1) * (pIp->mFWarning.countSPSeen == 0) * (pIp->mFWarning.countSPset == pIp_mFWarning_countSPset)) || (0 <= 33750 && pIp_mFWarning_countSPSeen + 1 > 2 && pIp_mFWarning_countSPLost != 0 && pIp_mDSSData_flgSP != 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == pIp_mFWarning_Wsp) * (pIp->mFWarning.countSPLost == 0) * (pIp->mFWarning.countSPSeen == 0) * (pIp->mFWarning.countSPset == pIp_mFWarning_countSPset)) || (0 <= 33750 && pIp_mFWarning_countSPSeen > 2 && pIp_mFWarning_countSPLost == 0 && pIp_mDSSData_flgSP != 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == pIp_mFWarning_Wsp) * (pIp->mFWarning.countSPLost == 0) * (pIp->mFWarning.countSPSeen == 0) * (pIp->mFWarning.countSPset == pIp_mFWarning_countSPset)) || (pIp_mFWarning_countSPLost <= 33750 && pIp_mFWarning_countSPSeen + 1 <= 2 && pIp_mFWarning_countSPLost != 0 && pIp_mDSSData_flgSP != 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == pIp_mFWarning_Wsp) * (pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost) * (pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen + 1) * (pIp->mFWarning.countSPset == pIp_mFWarning_countSPset)) || (pIp_mFWarning_countSPLost <= 33750 && pIp_mFWarning_countSPSeen <= 2 && pIp_mFWarning_countSPLost == 0 && pIp_mDSSData_flgSP != 0 && (pIp->mDSSData.flgSP == pIp_mDSSData_flgSP) * (pIp->mFWarning.Wsp == pIp_mFWarning_Wsp) * (pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost) * (pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen) * (pIp->mFWarning.countSPset == pIp_mFWarning_countSPset))
*/
{

    if (pIp -> mDSSData.flgSP == 0)
    {
     pIp -> mFWarning.countSPLost++ ;
     pIp -> mFWarning.countSPSeen = 0 ;
    }
    else
    {

     if (pIp -> mFWarning.countSPLost != 0)

     {
      pIp -> mFWarning.countSPSeen++ ;
     }


     if (pIp -> mFWarning.countSPSeen > 2)

     {
      pIp -> mFWarning.countSPLost = 0 ;
      pIp -> mFWarning.countSPSeen = 0 ;
     }

    }

    if (pIp -> mFWarning.countSPLost > 33750)
    {
     pIp -> mFWarning.Wsp = 0xEB ;
     pIp -> mFWarning.countSPLost = 0 ;
     pIp -> mFWarning.countSPset = 0 ;
    }

    return ;
}
void main44(SoftFaultJudgeSP *pIp)

/*@
With pIp_mDSSData_flgSP pIp_mFWarning_Wsp pIp_mFWarning_countSPLost pIp_mFWarning_countSPSeen pIp_mFWarning_countSPset
Require pIp->mDSSData.flgSP == pIp_mDSSData_flgSP && pIp->mFWarning.Wsp == pIp_mFWarning_Wsp && pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost && pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen && pIp->mFWarning.countSPset == pIp_mFWarning_countSPset
Ensure emp
*/{

    pIp -> mDSSData.flgSP = 1;
    pIp -> mFWarning.countSPLost = 1;
    pIp -> mFWarning.countSPSeen = 0;
    
    SoftFaultJudgeSPFun(pIp);

    
    


}