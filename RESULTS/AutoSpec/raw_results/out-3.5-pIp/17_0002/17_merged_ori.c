
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
ensures pIp- > mDSSData.stateFlag_B == 1;
ensures pIp- > mDSSData.stateFlag_B == 0;
ensures pIp- > mDSSData.stateFlag_A == 0;
ensures \old(pIp->mDSSData.stateFlag_A) == 1 ==> pIp->mDSSData.stateFlag_A == 0;
ensures \old(pIp->mDSSData.stateFlag_A) != 1 ==> pIp->mDSSData.stateFlag_A == 1;
disjoint behaviors case_0x33, case_other;
complete behaviors case_0x33, case_other;
behavior case_other:;
behavior case_0x33:;
assumes pIp- > flgSP == 0x33;
assumes pIp- > flgSP != 0x33;
assigns pIp- > mDSSData.stateFlag_A, pIp- > mDSSData.stateFlag_B;
```c;
```;
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


void main17(SwitchSS *pIp)
{

	pIp -> flgSP = 0x00;
	pIp -> mDSSData.stateFlag_A = 0;
    pIp -> mDSSData.stateFlag_B = 0;

	SwitchSSFun(pIp);

    // @ assert pIp -> mDSSData.stateFlag_A == 0;
    // @ assert pIp -> mDSSData.stateFlag_B == 0;
    // @ assert pIp -> flgSP == 0x00;

}