
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

/*@
requires \valid(pIp) && \valid(pIp->mThrDistribute.stateFlag+ (0..1)) ;

ensures pIp->mThrDistribute.stateFlag[1] == 1 && pIp->mThrDistribute.stateFlag[0] == 1 ==> pIp->mThrDistribute.flgABChoose == 0xCC && pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);

ensures pIp->mThrDistribute.stateFlag[0] == 0 && pIp->mThrDistribute.stateFlag[1] == 1 ==> pIp->mThrDistribute.flgABChoose == 0x33 && pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);

ensures pIp->mThrDistribute.stateFlag[0] != 0 && pIp->mThrDistribute.stateFlag[0] != 1 ==> pIp->mThrDistribute.flgABChoose == 0 && pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);

ensures pIp->mThrDistribute.stateFlag[1] != 1 && pIp->mThrDistribute.stateFlag[0] == 0 && pIp->mThrDistribute.stateFlag[0] != 1 ==> pIp->mThrDistribute.flgABChoose == 0 && pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);

ensures pIp->mThrDistribute.stateFlag[0] != 0 && pIp->mThrDistribute.stateFlag[1] != 1 && pIp->mThrDistribute.stateFlag[0] == 1 ==> pIp->mThrDistribute.flgABChoose == 0 && pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);

assigns pIp->mThrDistribute.flgABChoose, pIp->mThrDistribute.wPulse;
*/

void ThrABAutoChooseFun(ThrABAutoChoose *pIp)
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
}/*@
    requires \valid(pIp) && \valid(pIp->mThrDistribute.stateFlag+ (0..1)) ;
    */
    
void main6(ThrABAutoChoose *pIp)
{
	pIp -> mThrDistribute.stateFlag[0] = 0;
	pIp -> mThrDistribute.stateFlag[1] = 1;

	ThrABAutoChooseFun(pIp);

    /*@ assert pIp -> mThrDistribute.flgABChoose == 0x33; */    
}
