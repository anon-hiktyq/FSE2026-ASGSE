
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
```c
requires \valid(pIp);
ensures ((\old(pIp->mThrDistribute.stateFlag[0]) == 1) && (\old(pIp->mThrDistribute.stateFlag[1]) == 1)) ==> 
        (pIp->mThrDistribute.flgABChoose == 0xCC);
ensures ((\old(pIp->mThrDistribute.stateFlag[0]) == 0) && (\old(pIp->mThrDistribute.stateFlag[1]) == 1)) ==> 
        (pIp->mThrDistribute.flgABChoose == 0x33);
ensures !((\old(pIp->mThrDistribute.stateFlag[0]) == 1) && (\old(pIp->mThrDistribute.stateFlag[1]) == 1)) &&
        !((\old(pIp->mThrDistribute.stateFlag[0]) == 0) && (\old(pIp->mThrDistribute.stateFlag[1]) == 1)) ==> 
        (pIp->mThrDistribute.flgABChoose == 0x00);
ensures pIp->mThrDistribute.stateFlag[0] == \old(pIp->mThrDistribute.stateFlag[0]);
ensures pIp->mThrDistribute.stateFlag[1] == \old(pIp->mThrDistribute.stateFlag[1]);
ensures pIp->mThrDistribute.wPulse == \old(pIp->mThrDistribute.wPulse);
assigns pIp->mThrDistribute.flgABChoose;
```
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


void main9(ThrABAutoChoose *pIp)
{

	pIp -> mThrDistribute.stateFlag[0] = 0;
	pIp -> mThrDistribute.stateFlag[1] = 1;

	ThrABAutoChooseFun(pIp);

    // @ assert pIp -> mThrDistribute.flgABChoose == 0x33; 
    // @ assert pIp -> mThrDistribute.stateFlag[0] == 0;    
    // @ assert pIp -> mThrDistribute.stateFlag[1] == 1; 
    // @ assert pIp -> mThrDistribute.wPulse == \at(pIp -> mThrDistribute.wPulse, Pre);  
    

}