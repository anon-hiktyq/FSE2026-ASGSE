
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    typedef struct TAG_DIGITAL_GYRO_DATA
{

    int		countPick[9];		 
    int 	Gi[3];				 	
    int 	wa[9];				 	
    int 	wal[9];				 
 	int		JoinTotal;           	
 	int 	gyroStatus0;		 	
 	int 	gyroStatus1;		 
    int 	W[3];				 	
    int		SignFlag[9] ; 		 	 
	int 	Rtemp[3][5];		 	
	int		stateFlag[9];
	int     tmpwa[5];	
	
} SGyroData;
typedef struct __CalculateGyroDg
{

	SGyroData*			pGyroData;

} CalculateGyroDg;


void MatrixMulti(SGyroData *pIp)
/*@
With pIp_countPick_l pIp_countPick_0 pIp_countPick_1 pIp_countPick_2 pIp_countPick_3 pIp_countPick_4 pIp_countPick_5 pIp_countPick_6 pIp_countPick_7 pIp_countPick_8 pIp_Gi_l pIp_Gi_0 pIp_Gi_1 pIp_Gi_2 pIp_wa_l pIp_wa_0 pIp_wa_1 pIp_wa_2 pIp_wa_3 pIp_wa_4 pIp_wa_5 pIp_wa_6 pIp_wa_7 pIp_wa_8 pIp_wal_l pIp_wal_0 pIp_wal_1 pIp_wal_2 pIp_wal_3 pIp_wal_4 pIp_wal_5 pIp_wal_6 pIp_wal_7 pIp_wal_8 pIp_JoinTotal pIp_gyroStatus0 pIp_gyroStatus1 pIp_W_l pIp_W_0 pIp_W_1 pIp_W_2 pIp_SignFlag_l pIp_SignFlag_0 pIp_SignFlag_1 pIp_SignFlag_2 pIp_SignFlag_3 pIp_SignFlag_4 pIp_SignFlag_5 pIp_SignFlag_6 pIp_SignFlag_7 pIp_SignFlag_8 pIp_Rtemp_l pIp_Rtemp_0 pIp_Rtemp_1 pIp_Rtemp_2 pIp_stateFlag_l pIp_stateFlag_0 pIp_stateFlag_1 pIp_stateFlag_2 pIp_stateFlag_3 pIp_stateFlag_4 pIp_stateFlag_5 pIp_stateFlag_6 pIp_stateFlag_7 pIp_stateFlag_8 pIp_tmpwa_l pIp_tmpwa_0 pIp_tmpwa_1 pIp_tmpwa_2 pIp_tmpwa_3 pIp_tmpwa_4
Require store_int_array(pIp->countPick,9, pIp_countPick_l) && pIp_countPick_l[0] == pIp_countPick_0 && pIp_countPick_l[1] == pIp_countPick_1 && pIp_countPick_l[2] == pIp_countPick_2 && pIp_countPick_l[3] == pIp_countPick_3 && pIp_countPick_l[4] == pIp_countPick_4 && pIp_countPick_l[5] == pIp_countPick_5 && pIp_countPick_l[6] == pIp_countPick_6 && pIp_countPick_l[7] == pIp_countPick_7 && pIp_countPick_l[8] == pIp_countPick_8 && store_int_array(pIp->Gi,3, pIp_Gi_l) && pIp_Gi_l[0] == pIp_Gi_0 && pIp_Gi_l[1] == pIp_Gi_1 && pIp_Gi_l[2] == pIp_Gi_2 && store_int_array(pIp->wa,9, pIp_wa_l) && pIp_wa_l[0] == pIp_wa_0 && pIp_wa_l[1] == pIp_wa_1 && pIp_wa_l[2] == pIp_wa_2 && pIp_wa_l[3] == pIp_wa_3 && pIp_wa_l[4] == pIp_wa_4 && pIp_wa_l[5] == pIp_wa_5 && pIp_wa_l[6] == pIp_wa_6 && pIp_wa_l[7] == pIp_wa_7 && pIp_wa_l[8] == pIp_wa_8 && store_int_array(pIp->wal,9, pIp_wal_l) && pIp_wal_l[0] == pIp_wal_0 && pIp_wal_l[1] == pIp_wal_1 && pIp_wal_l[2] == pIp_wal_2 && pIp_wal_l[3] == pIp_wal_3 && pIp_wal_l[4] == pIp_wal_4 && pIp_wal_l[5] == pIp_wal_5 && pIp_wal_l[6] == pIp_wal_6 && pIp_wal_l[7] == pIp_wal_7 && pIp_wal_l[8] == pIp_wal_8 && pIp->JoinTotal == pIp_JoinTotal && pIp->gyroStatus0 == pIp_gyroStatus0 && pIp->gyroStatus1 == pIp_gyroStatus1 && store_int_array(pIp->W,3, pIp_W_l) && pIp_W_l[0] == pIp_W_0 && pIp_W_l[1] == pIp_W_1 && pIp_W_l[2] == pIp_W_2 && store_int_array(pIp->SignFlag,9, pIp_SignFlag_l) && pIp_SignFlag_l[0] == pIp_SignFlag_0 && pIp_SignFlag_l[1] == pIp_SignFlag_1 && pIp_SignFlag_l[2] == pIp_SignFlag_2 && pIp_SignFlag_l[3] == pIp_SignFlag_3 && pIp_SignFlag_l[4] == pIp_SignFlag_4 && pIp_SignFlag_l[5] == pIp_SignFlag_5 && pIp_SignFlag_l[6] == pIp_SignFlag_6 && pIp_SignFlag_l[7] == pIp_SignFlag_7 && pIp_SignFlag_l[8] == pIp_SignFlag_8 && store_int_array(pIp->Rtemp,3, pIp_Rtemp_l) && pIp_Rtemp_l[0] == pIp_Rtemp_0 && pIp_Rtemp_l[1] == pIp_Rtemp_1 && pIp_Rtemp_l[2] == pIp_Rtemp_2 && store_int_array(pIp->stateFlag,9, pIp_stateFlag_l) && pIp_stateFlag_l[0] == pIp_stateFlag_0 && pIp_stateFlag_l[1] == pIp_stateFlag_1 && pIp_stateFlag_l[2] == pIp_stateFlag_2 && pIp_stateFlag_l[3] == pIp_stateFlag_3 && pIp_stateFlag_l[4] == pIp_stateFlag_4 && pIp_stateFlag_l[5] == pIp_stateFlag_5 && pIp_stateFlag_l[6] == pIp_stateFlag_6 && pIp_stateFlag_l[7] == pIp_stateFlag_7 && pIp_stateFlag_l[8] == pIp_stateFlag_8 && store_int_array(pIp->tmpwa,5, pIp_tmpwa_l) && pIp_tmpwa_l[0] == pIp_tmpwa_0 && pIp_tmpwa_l[1] == pIp_tmpwa_1 && pIp_tmpwa_l[2] == pIp_tmpwa_2 && pIp_tmpwa_l[3] == pIp_tmpwa_3 && pIp_tmpwa_l[4] == pIp_tmpwa_4
Ensure emp
*/
{

    int ir =0;
    int jc =0;
    int nk =0;
    int index=0 ;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 

  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (; ir< 3; ir++)
    {
        jc = 0;
       
  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 

  /*@ Print user assertion at number LoopEntry_1*/ 
/*@ Inv emp */ /*1*/ 
 for (; jc< 1; jc++)
        {
            index = ir * 1 + jc ;

            pIp -> pGyroData->W[index] = 0 ;

            nk = 0;
           
  /*@ Print user assertion at number LoopEntry_2*/ 
/*@ Inv emp */ /*2*/ 

  /*@ Print user assertion at number LoopEntry_2*/ 
/*@ Inv emp */ /*2*/ 
 for (; nk< 5; nk++)
            {
                pIp -> pGyroData->W[index] = pIp -> pGyroData->W[index] + pIp->pGyroData->Rtemp[ir * 5 + nk] * pIp->tmpwa[nk * 1 + jc] ;
            }
        }
    }

    return ;
}
void CalculateGyroDgFun(CalculateGyroDg *pIp)

/*@
With pIp_pGyroData_countPick_l pIp_pGyroData_countPick_0 pIp_pGyroData_countPick_1 pIp_pGyroData_countPick_2 pIp_pGyroData_countPick_3 pIp_pGyroData_countPick_4 pIp_pGyroData_countPick_5 pIp_pGyroData_countPick_6 pIp_pGyroData_countPick_7 pIp_pGyroData_countPick_8 pIp_pGyroData_Gi_l pIp_pGyroData_Gi_0 pIp_pGyroData_Gi_1 pIp_pGyroData_Gi_2 pIp_pGyroData_wa_l pIp_pGyroData_wa_0 pIp_pGyroData_wa_1 pIp_pGyroData_wa_2 pIp_pGyroData_wa_3 pIp_pGyroData_wa_4 pIp_pGyroData_wa_5 pIp_pGyroData_wa_6 pIp_pGyroData_wa_7 pIp_pGyroData_wa_8 pIp_pGyroData_wal_l pIp_pGyroData_wal_0 pIp_pGyroData_wal_1 pIp_pGyroData_wal_2 pIp_pGyroData_wal_3 pIp_pGyroData_wal_4 pIp_pGyroData_wal_5 pIp_pGyroData_wal_6 pIp_pGyroData_wal_7 pIp_pGyroData_wal_8 pIp_pGyroData_JoinTotal pIp_pGyroData_gyroStatus0 pIp_pGyroData_gyroStatus1 pIp_pGyroData_W_l pIp_pGyroData_W_0 pIp_pGyroData_W_1 pIp_pGyroData_W_2 pIp_pGyroData_SignFlag_l pIp_pGyroData_SignFlag_0 pIp_pGyroData_SignFlag_1 pIp_pGyroData_SignFlag_2 pIp_pGyroData_SignFlag_3 pIp_pGyroData_SignFlag_4 pIp_pGyroData_SignFlag_5 pIp_pGyroData_SignFlag_6 pIp_pGyroData_SignFlag_7 pIp_pGyroData_SignFlag_8 pIp_pGyroData_Rtemp_l pIp_pGyroData_Rtemp_0 pIp_pGyroData_Rtemp_1 pIp_pGyroData_Rtemp_2 pIp_pGyroData_stateFlag_l pIp_pGyroData_stateFlag_0 pIp_pGyroData_stateFlag_1 pIp_pGyroData_stateFlag_2 pIp_pGyroData_stateFlag_3 pIp_pGyroData_stateFlag_4 pIp_pGyroData_stateFlag_5 pIp_pGyroData_stateFlag_6 pIp_pGyroData_stateFlag_7 pIp_pGyroData_stateFlag_8 pIp_pGyroData_tmpwa_l pIp_pGyroData_tmpwa_0 pIp_pGyroData_tmpwa_1 pIp_pGyroData_tmpwa_2 pIp_pGyroData_tmpwa_3 pIp_pGyroData_tmpwa_4
Require store_int_array(pIp->pGyroData->countPick,9, pIp_pGyroData_countPick_l) && pIp_pGyroData_countPick_l[0] == pIp_pGyroData_countPick_0 && pIp_pGyroData_countPick_l[1] == pIp_pGyroData_countPick_1 && pIp_pGyroData_countPick_l[2] == pIp_pGyroData_countPick_2 && pIp_pGyroData_countPick_l[3] == pIp_pGyroData_countPick_3 && pIp_pGyroData_countPick_l[4] == pIp_pGyroData_countPick_4 && pIp_pGyroData_countPick_l[5] == pIp_pGyroData_countPick_5 && pIp_pGyroData_countPick_l[6] == pIp_pGyroData_countPick_6 && pIp_pGyroData_countPick_l[7] == pIp_pGyroData_countPick_7 && pIp_pGyroData_countPick_l[8] == pIp_pGyroData_countPick_8 && store_int_array(pIp->pGyroData->Gi,3, pIp_pGyroData_Gi_l) && pIp_pGyroData_Gi_l[0] == pIp_pGyroData_Gi_0 && pIp_pGyroData_Gi_l[1] == pIp_pGyroData_Gi_1 && pIp_pGyroData_Gi_l[2] == pIp_pGyroData_Gi_2 && store_int_array(pIp->pGyroData->wa,9, pIp_pGyroData_wa_l) && pIp_pGyroData_wa_l[0] == pIp_pGyroData_wa_0 && pIp_pGyroData_wa_l[1] == pIp_pGyroData_wa_1 && pIp_pGyroData_wa_l[2] == pIp_pGyroData_wa_2 && pIp_pGyroData_wa_l[3] == pIp_pGyroData_wa_3 && pIp_pGyroData_wa_l[4] == pIp_pGyroData_wa_4 && pIp_pGyroData_wa_l[5] == pIp_pGyroData_wa_5 && pIp_pGyroData_wa_l[6] == pIp_pGyroData_wa_6 && pIp_pGyroData_wa_l[7] == pIp_pGyroData_wa_7 && pIp_pGyroData_wa_l[8] == pIp_pGyroData_wa_8 && store_int_array(pIp->pGyroData->wal,9, pIp_pGyroData_wal_l) && pIp_pGyroData_wal_l[0] == pIp_pGyroData_wal_0 && pIp_pGyroData_wal_l[1] == pIp_pGyroData_wal_1 && pIp_pGyroData_wal_l[2] == pIp_pGyroData_wal_2 && pIp_pGyroData_wal_l[3] == pIp_pGyroData_wal_3 && pIp_pGyroData_wal_l[4] == pIp_pGyroData_wal_4 && pIp_pGyroData_wal_l[5] == pIp_pGyroData_wal_5 && pIp_pGyroData_wal_l[6] == pIp_pGyroData_wal_6 && pIp_pGyroData_wal_l[7] == pIp_pGyroData_wal_7 && pIp_pGyroData_wal_l[8] == pIp_pGyroData_wal_8 && pIp->pGyroData->JoinTotal == pIp_pGyroData_JoinTotal && pIp->pGyroData->gyroStatus0 == pIp_pGyroData_gyroStatus0 && pIp->pGyroData->gyroStatus1 == pIp_pGyroData_gyroStatus1 && store_int_array(pIp->pGyroData->W,3, pIp_pGyroData_W_l) && pIp_pGyroData_W_l[0] == pIp_pGyroData_W_0 && pIp_pGyroData_W_l[1] == pIp_pGyroData_W_1 && pIp_pGyroData_W_l[2] == pIp_pGyroData_W_2 && store_int_array(pIp->pGyroData->SignFlag,9, pIp_pGyroData_SignFlag_l) && pIp_pGyroData_SignFlag_l[0] == pIp_pGyroData_SignFlag_0 && pIp_pGyroData_SignFlag_l[1] == pIp_pGyroData_SignFlag_1 && pIp_pGyroData_SignFlag_l[2] == pIp_pGyroData_SignFlag_2 && pIp_pGyroData_SignFlag_l[3] == pIp_pGyroData_SignFlag_3 && pIp_pGyroData_SignFlag_l[4] == pIp_pGyroData_SignFlag_4 && pIp_pGyroData_SignFlag_l[5] == pIp_pGyroData_SignFlag_5 && pIp_pGyroData_SignFlag_l[6] == pIp_pGyroData_SignFlag_6 && pIp_pGyroData_SignFlag_l[7] == pIp_pGyroData_SignFlag_7 && pIp_pGyroData_SignFlag_l[8] == pIp_pGyroData_SignFlag_8 && store_int_array(pIp->pGyroData->Rtemp,3, pIp_pGyroData_Rtemp_l) && pIp_pGyroData_Rtemp_l[0] == pIp_pGyroData_Rtemp_0 && pIp_pGyroData_Rtemp_l[1] == pIp_pGyroData_Rtemp_1 && pIp_pGyroData_Rtemp_l[2] == pIp_pGyroData_Rtemp_2 && store_int_array(pIp->pGyroData->stateFlag,9, pIp_pGyroData_stateFlag_l) && pIp_pGyroData_stateFlag_l[0] == pIp_pGyroData_stateFlag_0 && pIp_pGyroData_stateFlag_l[1] == pIp_pGyroData_stateFlag_1 && pIp_pGyroData_stateFlag_l[2] == pIp_pGyroData_stateFlag_2 && pIp_pGyroData_stateFlag_l[3] == pIp_pGyroData_stateFlag_3 && pIp_pGyroData_stateFlag_l[4] == pIp_pGyroData_stateFlag_4 && pIp_pGyroData_stateFlag_l[5] == pIp_pGyroData_stateFlag_5 && pIp_pGyroData_stateFlag_l[6] == pIp_pGyroData_stateFlag_6 && pIp_pGyroData_stateFlag_l[7] == pIp_pGyroData_stateFlag_7 && pIp_pGyroData_stateFlag_l[8] == pIp_pGyroData_stateFlag_8 && store_int_array(pIp->pGyroData->tmpwa,5, pIp_pGyroData_tmpwa_l) && pIp_pGyroData_tmpwa_l[0] == pIp_pGyroData_tmpwa_0 && pIp_pGyroData_tmpwa_l[1] == pIp_pGyroData_tmpwa_1 && pIp_pGyroData_tmpwa_l[2] == pIp_pGyroData_tmpwa_2 && pIp_pGyroData_tmpwa_l[3] == pIp_pGyroData_tmpwa_3 && pIp_pGyroData_tmpwa_l[4] == pIp_pGyroData_tmpwa_4
Ensure emp
*/{

 	int j = 0;
	int k = 0;


 	/*@ Print user assertion at number LoopEntry_3*/ 
/*@ Inv emp */ /*3*/ 
 for (; j < 5 ; j++ )
	{
	     pIp->tmpwa[j] = 0 ;
    }

	j = 0;


 	/*@ Print user assertion at number LoopEntry_4*/ 
/*@ Inv emp */ /*4*/ 
 for (; j < pIp -> pGyroData->JoinTotal ; j++ )
	{
		k = pIp -> pGyroData->SignFlag[j] ;
		pIp->tmpwa[j] = pIp -> pGyroData->wa[k] ;
	}


	if ( pIp -> pGyroData->JoinTotal >= 3 )
	{

		MatrixMulti(pIp);
	
	}

	else
	{
		pIp -> pGyroData->W[0] = 0 ;
		pIp -> pGyroData->W[1] = 0 ;
		pIp -> pGyroData->W[2] = 0 ;
	}

	return;
}