
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
requires \valid(pIp);
requires \valid(pIp->mThrDistribute.stateFlag+(0..1));
ensures pIp->mThrDistribute.stateFlag[1] == 1 && pIp->mThrDistribute.stateFlag[0] == 1 ==> 
        pIp->mThrDistribute.flgABChoose == 204 && 
        pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);
ensures pIp->mThrDistribute.stateFlag[1] == 1 && pIp->mThrDistribute.stateFlag[0] == 0 && 
        pIp->mThrDistribute.stateFlag[0] != 1 ==> 
        pIp->mThrDistribute.flgABChoose == 51 && 
        pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);
ensures pIp->mThrDistribute.stateFlag[0] != 0 && pIp->mThrDistribute.stateFlag[0] != 1 ==> 
        pIp->mThrDistribute.flgABChoose == 0 && 
        pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);
ensures pIp->mThrDistribute.stateFlag[1] != 1 && pIp->mThrDistribute.stateFlag[0] == 0 && 
        pIp->mThrDistribute.stateFlag[0] != 1 ==> 
        pIp->mThrDistribute.flgABChoose == 0 && 
        pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);
ensures pIp->mThrDistribute.stateFlag[0] != 0 && pIp->mThrDistribute.stateFlag[1] != 1 && 
        pIp->mThrDistribute.stateFlag[0] == 1 ==> 
        pIp->mThrDistribute.flgABChoose == 0 && 
        pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);
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
}

/*@
requires \valid(pIp);
requires \valid(pIp->mThrDistribute.stateFlag+(0..1));
*/

void goo19(ThrABAutoChoose *pIp)
{
	pIp -> mThrDistribute.stateFlag[0] = 0;
	pIp -> mThrDistribute.stateFlag[1] = 0;

	ThrABAutoChooseFun(pIp);

    /*@ assert pIp -> mThrDistribute.flgABChoose == 0x00; */ 
    /*@ assert pIp -> mThrDistribute.stateFlag[0] == 0; */    
    /*@ assert pIp -> mThrDistribute.stateFlag[1] == 0; */ 
    /*@ assert pIp -> mThrDistribute.wPulse == \at(pIp -> mThrDistribute.wPulse, Pre); */  
    
}
