
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
requires pIp->mFWarning.countSPSeen >= 0;
requires pIp->mFWarning.countSPLost >= 0;
requires \valid(pIp);
pIp- > mFWarning.countSPset;
pIp- > mFWarning.countSPset == 0);
pIp- > mFWarning.countSPSeen,;
pIp- > mFWarning.countSPLost,;
pIp- > mFWarning.countSPLost == 0 &&;
pIp- > mFWarning.Wsp,;
ensures pIp->mFWarning.countSPSeen >= 0;
ensures pIp->mFWarning.countSPSeen > 2 ==> pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPSeen == 0;
ensures pIp->mFWarning.countSPLost >= 0;
ensures pIp->mFWarning.countSPLost > 33750 ==> pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPset == 0;
ensures pIp->mFWarning.countSPLost > 33750 ==> pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPset == 0;;
ensures pIp->mFWarning.countSPLost > 33750 ==> pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPset == 0;
ensures pIp->mFWarning.countSPLost > 33750 ==> (pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPLost == 0);
ensures pIp->mFWarning.countSPLost > 33750 ==> (pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPset == 0);
ensures pIp->mDSSData.flgSP == 0 ==> pIp->mFWarning.countSPSeen == 0;
ensures pIp->mDSSData.flgSP == 0 ==> pIp->mFWarning.countSPLost >= \old(pIp->mFWarning.countSPLost);
ensures pIp->mDSSData.flgSP == 0 ==> pIp->mFWarning.countSPLost > \old(pIp->mFWarning.countSPLost);
ensures pIp->mDSSData.flgSP == 0 ==> pIp->mFWarning.countSPLost == \old(pIp->mFWarning.countSPLost) + 1;
ensures pIp->mDSSData.flgSP == 0 ==> pIp->mFWarning.countSPLost == \old(pIp->mFWarning.countSPLost) + 1 && pIp->mFWarning.countSPSeen == 0;
ensures pIp->mDSSData.flgSP != 0 ==> (pIp->mFWarning.countSPSeen > 2 ==> pIp->mFWarning.countSPLost == 0);
ensures pIp->mDSSData.flgSP != 0 ==> (pIp->mFWarning.countSPLost == 0 || pIp->mFWarning.countSPLost == \old(pIp->mFWarning.countSPLost)) && (pIp->mFWarning.countSPSeen == 0 || pIp->mFWarning.countSPSeen == \old(pIp->mFWarning.countSPSeen) + 1);
ensures pIp->mDSSData.flgSP != 0 && \old(pIp->mFWarning.countSPLost) != 0 ==> pIp->mFWarning.countSPSeen > \old(pIp->mFWarning.countSPSeen);
ensures pIp->mDSSData.flgSP != 0 && \old(pIp->mFWarning.countSPLost) != 0 ==> pIp->mFWarning.countSPSeen == \old(pIp->mFWarning.countSPSeen) + 1;
ensures \result == 0;;
ensures (pIp->mFWarning.countSPLost > 33750) ==> (pIp->mFWarning.Wsp == 0xEB &&;
ensures (pIp->mFWarning.countSPLost > 33750) ==> (pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPset == 0);
ensures (pIp->mDSSData.flgSP == 0) ==> (pIp->mFWarning.countSPLost >= \old(pIp->mFWarning.countSPLost));
ensures (pIp->mDSSData.flgSP == 0 && \old(pIp->mFWarning.countSPLost) <= 33750) ==> pIp->mFWarning.countSPLost == \old(pIp->mFWarning.countSPLost) + 1;
ensures (pIp->mDSSData.flgSP != 0 && pIp->mFWarning.countSPLost != 0) ==> pIp->mFWarning.countSPSeen == \old(pIp->mFWarning.countSPSeen) + 1;
ensures (pIp->mDSSData.flgSP != 0 && \old(pIp->mFWarning.countSPLost) != 0) ==> pIp->mFWarning.countSPSeen == \old(pIp->mFWarning.countSPSeen) + 1;
ensures (pIp->mDSSData.flgSP != 0 && \old(pIp->mFWarning.countSPLost) != 0) ==> (pIp->mFWarning.countSPSeen >= \old(pIp->mFWarning.countSPSeen));
assigns pIp- > mFWarning.countSPLost,;
assigns pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.countSPset, pIp- > mFWarning.Wsp;
assigns pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.Wsp, pIp- > mFWarning.countSPset;
assigns pIp- > mFWarning.Wsp,;
assigns pIp- > mFWarning.Wsp, pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.countSPset;
assigns pIp- > mDSSData.flgSP, pIp- > mFWarning.Wsp, pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.countSPset;
&& (pIp- > mFWarning.countSPSeen == 0);
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
void main41(SoftFaultJudgeSP *pIp)
{

    pIp -> mDSSData.flgSP = 0;
    pIp -> mFWarning.countSPLost = 0;
    pIp -> mFWarning.countSPSeen = 0;
    
    SoftFaultJudgeSPFun(pIp);

    // @ assert pIp -> mFWarning.countSPLost == 1;
    // @ assert pIp -> mFWarning.countSPSeen == 0;

}
