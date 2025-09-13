
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

/*@
	requires \valid(pIp);
*/
/*@
pIp- > mFWarning.Wsp, pIp- > mFWarning.countSPset;
ensures pIp- > mFWarning.countSPset == 0;
ensures pIp- > mFWarning.countSPSeen == \old(pIp- > mFWarning.countSPSeen) + 1;
ensures pIp- > mFWarning.countSPSeen == 0;
ensures pIp- > mFWarning.countSPSeen <= 3 ||;
ensures pIp- > mFWarning.countSPLost == \old(pIp- > mFWarning.countSPLost) + 1;
ensures pIp- > mFWarning.countSPLost == 0;
ensures pIp- > mFWarning.Wsp == 0xEB;
ensures \valid(pIp);
behavior sp_not_detected:;
behavior sp_lost_overflow:;
behavior sp_detected_with_previous_loss:;
assumes pIp- > mDSSData.flgSP == 0;
assumes pIp- > mDSSData.flgSP != 0 && pIp- > mFWarning.countSPLost != 0;
assumes \old(pIp->mFWarning.countSPLost) > 33750;
assigns pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen,;
(pIp- > mFWarning.countSPLost == 0 && pIp- > mFWarning.countSPSeen == 0);
*/
void SoftFaultJudgeSPFun(SoftFaultJudgeSP *pIp)

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

/*@
	requires \valid(pIp);
*/
void main44(SoftFaultJudgeSP *pIp)
{

    pIp -> mDSSData.flgSP = 1;
    pIp -> mFWarning.countSPLost = 1;
    pIp -> mFWarning.countSPSeen = 0;
    
    SoftFaultJudgeSPFun(pIp);

    // @ assert pIp -> mFWarning.countSPLost == 1;
    // @ assert pIp -> mFWarning.countSPSeen == 1;


}
