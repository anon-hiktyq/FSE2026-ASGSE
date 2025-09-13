
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
requires \valid(pIp);
ensures pIp- > mFWarning.countSPSeen == \old(pIp- > mFWarning.countSPSeen);
ensures pIp- > mFWarning.countSPSeen == \old(pIp- > mFWarning.countSPSeen) + 1;
ensures pIp- > mFWarning.countSPSeen == 0;
ensures pIp- > mFWarning.countSPLost == \old(pIp- > mFWarning.countSPLost);
ensures pIp- > mFWarning.countSPLost == \old(pIp- > mFWarning.countSPLost) + 1;
ensures \old(pIp->mFWarning.countSPSeen) > 2 && pIp->mDSSData.flgSP != 0 && \old(pIp->mFWarning.countSPLost) != 0 ==> pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPSeen == 0;
ensures \old(pIp->mFWarning.countSPLost) > 33750 ==> pIp->mFWarning.Wsp == 0xEB && pIp->mFWarning.countSPLost == 0 && pIp->mFWarning.countSPset == 0;
disjoint behaviors;
complete behaviors;
behavior flgSP_zero:;
behavior flgSP_nonzero_and_countSPLost_zero:;
behavior flgSP_nonzero_and_countSPLost_nonzero:;
assumes pIp- > mDSSData.flgSP == 0;
assumes pIp- > mDSSData.flgSP != 0 && \old(pIp- > mFWarning.countSPLost) == 0;
assumes pIp- > mDSSData.flgSP != 0 && \old(pIp- > mFWarning.countSPLost) != 0;
assigns pIp- > mFWarning.Wsp, pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.countSPset;
```c;
```;
Looking at the function and the test case, I need to generate ACSL contracts that capture the behavior of `SoftFaultJudgeSPFun`.;
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
