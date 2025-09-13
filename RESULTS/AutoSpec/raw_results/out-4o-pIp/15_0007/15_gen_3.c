
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


/*@
requires \valid(pIp);
assigns pIp->mDSSData.stateFlag_A, pIp->mDSSData.stateFlag_B;
ensures pIp->flgSP != 0x33 ==> pIp->mDSSData.stateFlag_A == 0 && pIp->mDSSData.stateFlag_B == 0;
ensures pIp->flgSP == 0x33 ==> pIp->mDSSData.stateFlag_B == 1;
ensures pIp->flgSP == 0x33 && \old(pIp->mDSSData.stateFlag_A) == 1 ==> pIp->mDSSData.stateFlag_A == 0;
ensures pIp->flgSP == 0x33 && \old(pIp->mDSSData.stateFlag_A) == 0 ==> pIp->mDSSData.stateFlag_A == 1;
*/
void SwitchSSFun(SwitchSS *pIp)

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


void main15(SwitchSS *pIp)
{

	pIp -> flgSP = 0x33;
	pIp -> mDSSData.stateFlag_A = 0;
    pIp -> mDSSData.stateFlag_B = 0;

	SwitchSSFun(pIp);

    // @ assert pIp -> mDSSData.stateFlag_A == 1;
    // @ assert pIp -> mDSSData.stateFlag_B == 1;
    // @ assert pIp -> flgSP == 0x33;

}