
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
pIp- > mDSSData.stateFlag_B == 1;
pIp- > mDSSData.stateFlag_B == 0;
pIp- > mDSSData.stateFlag_A == 0 &&;
ensures pIp->flgSP == 0x33 ==> pIp->mDSSData.stateFlag_B == 1;
ensures pIp->flgSP == 0x33 ==> (pIp->mDSSData.stateFlag_A == \old(pIp->mDSSData.stateFlag_A) ? pIp->mDSSData.stateFlag_A == 0 : pIp->mDSSData.stateFlag_A == 1);
ensures pIp->flgSP == 0x33 ==> (pIp->mDSSData.stateFlag_A == \old(!\old(pIp->mDSSData.stateFlag_A)) && pIp->mDSSData.stateFlag_B == 1);
ensures pIp->flgSP == 0x33 ==> (;
ensures pIp->flgSP == 0x33 ==> ((\old(pIp->mDSSData.stateFlag_A) == 1) ? (pIp->mDSSData.stateFlag_A == 0) : (pIp->mDSSData.stateFlag_A == 1));
ensures pIp->flgSP == 0x33 && \old(pIp->mDSSData.stateFlag_A) == 1 ==> pIp->mDSSData.stateFlag_A == 0;
ensures pIp->flgSP == 0x33 && \old(pIp->mDSSData.stateFlag_A) != 1 ==> pIp->mDSSData.stateFlag_A == 1;
ensures pIp->flgSP != 0x33 ==> pIp->mDSSData.stateFlag_B == 0;
ensures pIp->flgSP != 0x33 ==> pIp->mDSSData.stateFlag_A == 0;
ensures pIp->flgSP != 0x33 ==> pIp->mDSSData.stateFlag_A == 0 && pIp->mDSSData.stateFlag_B == 0;
ensures pIp->flgSP != 0x33 ==> (pIp->mDSSData.stateFlag_A == 0 && pIp->mDSSData.stateFlag_B == 0);
ensures pIp->flgSP != 0x33 ==> (;
ensures pIp- > mDSSData.stateFlag_B == 1;
ensures pIp- > mDSSData.stateFlag_B == 0;
ensures pIp- > mDSSData.stateFlag_A == 0;
ensures pIp- > mDSSData.stateFlag_A == (pIp- > mDSSData.stateFlag_A \old() == 1 ? 0 : 1);
ensures pIp- > flgSP == 0x33 == >;
disjoint behaviors;
complete behaviors;
behavior flag_not_0x33:;
behavior flag_0x33:;
assumes pIp- > flgSP == 0x33;
assumes pIp- > flgSP != 0x33;
assigns pIp- > mDSSData.stateFlag_B;
assigns pIp- > mDSSData.stateFlag_A;
assigns pIp- > mDSSData.stateFlag_A, pIp- > mDSSData.stateFlag_B;
);
(pIp- > mDSSData.stateFlag_A == \old(pIp- > mDSSData.stateFlag_A) ? pIp- > mDSSData.stateFlag_A == 0 : pIp- > mDSSData.stateFlag_A == 1) &&;
(\old(pIp- > mDSSData.stateFlag_A) == 0 && pIp- > mDSSData.stateFlag_A == 1));
((\old(pIp- > mDSSData.stateFlag_A) == 1 && pIp- > mDSSData.stateFlag_A == 0) ||;
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