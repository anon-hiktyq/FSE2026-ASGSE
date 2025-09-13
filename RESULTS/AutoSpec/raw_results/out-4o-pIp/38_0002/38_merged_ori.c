

typedef struct TAG_FAULT_WARNING
{
	
    int countSPLost;				
    int countSPSeen;				
    int countSPset;					
    int countUPSpc;					
     
} SFWarning;


typedef struct TAG_FALSE_RATE_MODULATOR
{
	
	int 	u;						
	int 	r;						
	int 	Yp;						
	int 	Yn;						
	                            	
}SFratemodulator;


typedef struct TAG_DIGITAL_GYRO_DATA
{        
 	int  	gyroStatus0;		
 	int 	gyroStatus1;		 
	
} SGyroData;

typedef struct TAG_UPS_2MS
{	
	int flgABChoose;				
    int wPulse;         			
	int stateFlag[2];				
    
} SThrDistribute;


typedef struct __InitVar
{

	int		countInt32ms;
	int		countSate;
	int		countPublic;
	int		countMode;
	int		flgPRSAM;
	int		flgGryoCalc;
	int		flg160INT;
	SGyroData		mGyroData;
	SFratemodulator mModulator;
	SThrDistribute	mThrDistribute;
	SFWarning		mFWarning;

} InitVar;

/*@
requires \valid(pIp);
pIp- > mThrDistribute.wPulse,;
pIp- > mThrDistribute.wPulse, pIp- > mModulator.r, pIp- > flgGryoCalc;
pIp- > mModulator.r,;
pIp- > mGyroData.gyroStatus1,;
pIp- > mGyroData.gyroStatus0,;
pIp- > mFWarning.countUPSpc,;
pIp- > mFWarning.countSPset,;
pIp- > mFWarning.countSPSeen,;
pIp- > mFWarning.countSPLost,;
pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.countSPset, pIp- > mFWarning.countUPSpc,;
pIp- > mFWarning, pIp- > mThrDistribute.wPulse, pIp- > mModulator.r, pIp- > flgGryoCalc;
pIp- > flgPRSAM,;
pIp- > flgGryoCalc;
pIp- > countSate,;
pIp- > countSate, pIp- > countPublic, pIp- > countMode, pIp- > countInt32ms,;
pIp- > countPublic,;
pIp- > countMode,;
pIp- > countInt32ms,;
ensures pIp- > mThrDistribute.wPulse == 0x0;
ensures pIp- > mModulator.r == 0;
ensures pIp- > mGyroData.gyroStatus1 == 0;
ensures pIp- > mGyroData.gyroStatus0 == 0;
ensures pIp- > mFWarning.countUPSpc == 0;
ensures pIp- > mFWarning.countSPset == 0;
ensures pIp- > mFWarning.countSPSeen == 0;
ensures pIp- > mFWarning.countSPLost == 0;
ensures pIp- > flgPRSAM == 0x3333;
ensures pIp- > flgGryoCalc == 0;
ensures pIp- > flg160INT == 0x3333;
ensures pIp- > countSate == 0;
ensures pIp- > countPublic == 0;
ensures pIp- > countMode == 0;
ensures pIp- > countInt32ms == 0;
ensures \unchanged(pIp- > mThrDistribute.flgABChoose);
ensures \unchanged(pIp- > mModulator.u);
ensures \unchanged(pIp- > mModulator.Yp);
ensures \unchanged(pIp- > mModulator.Yn);
assigns pIp- > flg160INT,;
assigns pIp- > flg160INT, pIp- > flgPRSAM, pIp- > mGyroData.gyroStatus0, pIp- > mGyroData.gyroStatus1,;
assigns pIp- > flg160INT, pIp- > flgPRSAM, pIp- > mGyroData.gyroStatus0, pIp- > mGyroData.gyroStatus1, pIp- > countSate, pIp- > countPublic, pIp- > countMode, pIp- > countInt32ms, pIp- > mFWarning.countSPLost, pIp- > mFWarning.countSPSeen, pIp- > mFWarning.countSPset, pIp- > mFWarning.countUPSpc, pIp- > mThrDistribute.wPulse, pIp- > mModulator.r, pIp- > flgGryoCalc;
assigns pIp- > flg160INT, pIp- > flgPRSAM, pIp- > mGyroData, pIp- > countSate, pIp- > countPublic, pIp- > countMode, pIp- > countInt32ms,;
assigns *pIp;
*/
void InitVarFun(InitVar *pIp)
{

	pIp -> flg160INT = 0x3333 ;
	pIp -> flgPRSAM = 0x3333 ;

	pIp -> mGyroData.gyroStatus0 = 0 ;
	pIp -> mGyroData.gyroStatus1 = 0 ;

	pIp -> countSate    = 0 ;
	pIp -> countPublic  = 0 ;
	pIp -> countMode    = 0 ;
	pIp -> countInt32ms = 0 ;

	pIp -> mFWarning.countSPLost = 0 ;
	pIp -> mFWarning.countSPSeen = 0 ;
	pIp -> mFWarning.countSPset  = 0 ;
	pIp -> mFWarning.countUPSpc  = 0 ;

	pIp -> mThrDistribute.wPulse = 0x0 ;

	pIp -> mModulator.r = 0 ;

	pIp -> flgGryoCalc = 0 ;

	return;
}

void main38(InitVar *pIp)
{
    InitVarFun(pIp);
    // @ assert pIp -> mThrDistribute.flgABChoose == \at(pIp->mThrDistribute.flgABChoose,Pre);
    // @ assert pIp -> mModulator.r == \at(pIp->mModulator.r,Pre);
    // @ assert pIp -> mModulator.u == \at(pIp->mModulator.u,Pre);
    // @ assert pIp -> mModulator.Yp == \at(pIp->mModulator.Yp,Pre);
    // @ assert pIp -> mModulator.Yn == \at(pIp->mModulator.Yn,Pre);
}