
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

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


void InitVarFun(InitVar *pIp)
/*@
With pIp_countInt32ms pIp_countSate pIp_countPublic pIp_countMode pIp_flgPRSAM pIp_flgGryoCalc pIp_flg160INT pIp_mGyroData_gyroStatus0 pIp_mGyroData_gyroStatus1 pIp_mModulator_u pIp_mModulator_r pIp_mModulator_Yp pIp_mModulator_Yn pIp_mThrDistribute_flgABChoose pIp_mThrDistribute_wPulse pIp_mThrDistribute_stateFlag_l pIp_mFWarning_countSPLost pIp_mFWarning_countSPSeen pIp_mFWarning_countSPset pIp_mFWarning_countUPSpc
Require pIp->countInt32ms == pIp_countInt32ms && pIp->countSate == pIp_countSate && pIp->countPublic == pIp_countPublic && pIp->countMode == pIp_countMode && pIp->flgPRSAM == pIp_flgPRSAM && pIp->flgGryoCalc == pIp_flgGryoCalc && pIp->flg160INT == pIp_flg160INT && pIp->mGyroData.gyroStatus0 == pIp_mGyroData_gyroStatus0 && pIp->mGyroData.gyroStatus1 == pIp_mGyroData_gyroStatus1 && pIp->mModulator.u == pIp_mModulator_u && pIp->mModulator.r == pIp_mModulator_r && pIp->mModulator.Yp == pIp_mModulator_Yp && pIp->mModulator.Yn == pIp_mModulator_Yn && pIp->mThrDistribute.flgABChoose == pIp_mThrDistribute_flgABChoose && pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse && store_int_array(pIp->mThrDistribute.stateFlag,2, pIp_mThrDistribute_stateFlag_l) && pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost && pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen && pIp->mFWarning.countSPset == pIp_mFWarning_countSPset && pIp->mFWarning.countUPSpc == pIp_mFWarning_countUPSpc
Ensure ((pIp->countInt32ms == 0) * (pIp->countSate == 0) * (pIp->countPublic == 0) * (pIp->countMode == 0) * (pIp->flgPRSAM == 13107) * (pIp->flgGryoCalc == 0) * (pIp->flg160INT == 13107) * (pIp->mGyroData.gyroStatus0 == 0) * (pIp->mGyroData.gyroStatus1 == 0) * (pIp->mModulator.u == pIp_mModulator_u) * (pIp->mModulator.r == 0) * (pIp->mModulator.Yp == pIp_mModulator_Yp) * (pIp->mModulator.Yn == pIp_mModulator_Yn) * (pIp->mThrDistribute.flgABChoose == pIp_mThrDistribute_flgABChoose) * (pIp->mThrDistribute.wPulse == 0) * store_int_array(&pIp->mThrDistribute.stateFlag, 2, pIp_mThrDistribute_stateFlag_l) * (pIp->mFWarning.countSPLost == 0) * (pIp->mFWarning.countSPSeen == 0) * (pIp->mFWarning.countSPset == 0) * (pIp->mFWarning.countUPSpc == 0))
*/
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
void main40(InitVar *pIp)

/*@
With pIp_countInt32ms pIp_countSate pIp_countPublic pIp_countMode pIp_flgPRSAM pIp_flgGryoCalc pIp_flg160INT pIp_mGyroData_gyroStatus0 pIp_mGyroData_gyroStatus1 pIp_mModulator_u pIp_mModulator_r pIp_mModulator_Yp pIp_mModulator_Yn pIp_mThrDistribute_flgABChoose pIp_mThrDistribute_wPulse pIp_mThrDistribute_stateFlag_l pIp_mFWarning_countSPLost pIp_mFWarning_countSPSeen pIp_mFWarning_countSPset pIp_mFWarning_countUPSpc
Require pIp->countInt32ms == pIp_countInt32ms && pIp->countSate == pIp_countSate && pIp->countPublic == pIp_countPublic && pIp->countMode == pIp_countMode && pIp->flgPRSAM == pIp_flgPRSAM && pIp->flgGryoCalc == pIp_flgGryoCalc && pIp->flg160INT == pIp_flg160INT && pIp->mGyroData.gyroStatus0 == pIp_mGyroData_gyroStatus0 && pIp->mGyroData.gyroStatus1 == pIp_mGyroData_gyroStatus1 && pIp->mModulator.u == pIp_mModulator_u && pIp->mModulator.r == pIp_mModulator_r && pIp->mModulator.Yp == pIp_mModulator_Yp && pIp->mModulator.Yn == pIp_mModulator_Yn && pIp->mThrDistribute.flgABChoose == pIp_mThrDistribute_flgABChoose && pIp->mThrDistribute.wPulse == pIp_mThrDistribute_wPulse && store_int_array(pIp->mThrDistribute.stateFlag,2, pIp_mThrDistribute_stateFlag_l) && pIp->mFWarning.countSPLost == pIp_mFWarning_countSPLost && pIp->mFWarning.countSPSeen == pIp_mFWarning_countSPSeen && pIp->mFWarning.countSPset == pIp_mFWarning_countSPset && pIp->mFWarning.countUPSpc == pIp_mFWarning_countUPSpc
Ensure emp
*/{
    InitVarFun(pIp);
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    

}