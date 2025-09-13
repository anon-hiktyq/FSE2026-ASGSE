
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
Looking at this code, I need to generate ACSL function contracts for `SwitchSSFun`. Based on the function logic and the assertions in `main16`, here's the contract:

```c
requires \valid(pIp);
behavior special_case:
    assumes pIp->flgSP == 0x33;
    ensures pIp->mDSSData.stateFlag_A == (1 - \old(pIp->mDSSData.stateFlag_A));
    ensures pIp->mDSSData.stateFlag_B == 1;
    ensures pIp->flgSP == \old(pIp->flgSP);
behavior default_case:
    assumes pIp->flgSP != 0x33;
    ensures pIp->mDSSData.stateFlag_A == 0;
    ensures pIp->mDSSData.stateFlag_B == 0;
    ensures pIp->flgSP == \old(pIp->flgSP);
assigns pIp->mDSSData.stateFlag_A, pIp->mDSSData.stateFlag_B;
```
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

    // @ assert pIp -> mDSSData.stateFlag_A == 0;
    // @ assert pIp -> mDSSData.stateFlag_B == 1;
    // @ assert pIp -> flgSP == 0x33;

}