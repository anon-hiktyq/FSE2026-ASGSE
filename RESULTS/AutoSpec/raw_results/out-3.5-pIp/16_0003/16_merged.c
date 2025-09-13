
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
behavior sp_flag_set:
    assumes pIp->flgSP == 0x33;
    ensures pIp->mDSSData.stateFlag_B == 1;
    ensures pIp->flgSP == \old(pIp->flgSP);
behavior sp_flag_unset:
    assumes pIp->flgSP != 0x33;
    ensures pIp->mDSSData.stateFlag_A == 0;
    ensures pIp->mDSSData.stateFlag_B == 0;
    ensures pIp->flgSP == \old(pIp->flgSP);
complete behaviors sp_flag_set, sp_flag_unset;
disjoint behaviors sp_flag_set, sp_flag_unset;
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


void main16(SwitchSS *pIp)
{

	pIp -> flgSP = 0x33;
	pIp -> mDSSData.stateFlag_A = 1;
    pIp -> mDSSData.stateFlag_B = 0;

	SwitchSSFun(pIp);

    //@ assert pIp -> mDSSData.stateFlag_A == 0;
    //@ assert pIp -> mDSSData.stateFlag_B == 1;
    //@ assert pIp -> flgSP == 0x33;

}