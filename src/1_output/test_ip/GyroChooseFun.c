
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
typedef struct __GyroChoose
{
    /* 输入端口 */
	/* 输出端口 */
	/* 输入输出端口 */
	SGyroData*			pGyroData;
	/* 状态变量 */
	/* 参数变量 */
} GyroChoose;

void GyroChooseFun(GyroChoose *pIp)

/*@
With pIp_pGyroData_countPick_l pIp_pGyroData_countPick_0 pIp_pGyroData_countPick_1 pIp_pGyroData_countPick_2 pIp_pGyroData_countPick_3 pIp_pGyroData_countPick_4 pIp_pGyroData_countPick_5 pIp_pGyroData_countPick_6 pIp_pGyroData_countPick_7 pIp_pGyroData_countPick_8 pIp_pGyroData_Gi_l pIp_pGyroData_Gi_0 pIp_pGyroData_Gi_1 pIp_pGyroData_Gi_2 pIp_pGyroData_wa_l pIp_pGyroData_wa_0 pIp_pGyroData_wa_1 pIp_pGyroData_wa_2 pIp_pGyroData_wa_3 pIp_pGyroData_wa_4 pIp_pGyroData_wa_5 pIp_pGyroData_wa_6 pIp_pGyroData_wa_7 pIp_pGyroData_wa_8 pIp_pGyroData_wal_l pIp_pGyroData_wal_0 pIp_pGyroData_wal_1 pIp_pGyroData_wal_2 pIp_pGyroData_wal_3 pIp_pGyroData_wal_4 pIp_pGyroData_wal_5 pIp_pGyroData_wal_6 pIp_pGyroData_wal_7 pIp_pGyroData_wal_8 pIp_pGyroData_JoinTotal pIp_pGyroData_gyroStatus0 pIp_pGyroData_gyroStatus1 pIp_pGyroData_W_l pIp_pGyroData_W_0 pIp_pGyroData_W_1 pIp_pGyroData_W_2 pIp_pGyroData_SignFlag_l pIp_pGyroData_SignFlag_0 pIp_pGyroData_SignFlag_1 pIp_pGyroData_SignFlag_2 pIp_pGyroData_SignFlag_3 pIp_pGyroData_SignFlag_4 pIp_pGyroData_SignFlag_5 pIp_pGyroData_SignFlag_6 pIp_pGyroData_SignFlag_7 pIp_pGyroData_SignFlag_8 pIp_pGyroData_Rtemp_l pIp_pGyroData_Rtemp_0 pIp_pGyroData_Rtemp_1 pIp_pGyroData_Rtemp_2 pIp_pGyroData_stateFlag_l pIp_pGyroData_stateFlag_0 pIp_pGyroData_stateFlag_1 pIp_pGyroData_stateFlag_2 pIp_pGyroData_stateFlag_3 pIp_pGyroData_stateFlag_4 pIp_pGyroData_stateFlag_5 pIp_pGyroData_stateFlag_6 pIp_pGyroData_stateFlag_7 pIp_pGyroData_stateFlag_8 pIp_pGyroData_tmpwa_l pIp_pGyroData_tmpwa_0 pIp_pGyroData_tmpwa_1 pIp_pGyroData_tmpwa_2 pIp_pGyroData_tmpwa_3 pIp_pGyroData_tmpwa_4
Require store_int_array(pIp->pGyroData->countPick,9, pIp_pGyroData_countPick_l) && pIp_pGyroData_countPick_l[0] == pIp_pGyroData_countPick_0 && pIp_pGyroData_countPick_l[1] == pIp_pGyroData_countPick_1 && pIp_pGyroData_countPick_l[2] == pIp_pGyroData_countPick_2 && pIp_pGyroData_countPick_l[3] == pIp_pGyroData_countPick_3 && pIp_pGyroData_countPick_l[4] == pIp_pGyroData_countPick_4 && pIp_pGyroData_countPick_l[5] == pIp_pGyroData_countPick_5 && pIp_pGyroData_countPick_l[6] == pIp_pGyroData_countPick_6 && pIp_pGyroData_countPick_l[7] == pIp_pGyroData_countPick_7 && pIp_pGyroData_countPick_l[8] == pIp_pGyroData_countPick_8 && store_int_array(pIp->pGyroData->Gi,3, pIp_pGyroData_Gi_l) && pIp_pGyroData_Gi_l[0] == pIp_pGyroData_Gi_0 && pIp_pGyroData_Gi_l[1] == pIp_pGyroData_Gi_1 && pIp_pGyroData_Gi_l[2] == pIp_pGyroData_Gi_2 && store_int_array(pIp->pGyroData->wa,9, pIp_pGyroData_wa_l) && pIp_pGyroData_wa_l[0] == pIp_pGyroData_wa_0 && pIp_pGyroData_wa_l[1] == pIp_pGyroData_wa_1 && pIp_pGyroData_wa_l[2] == pIp_pGyroData_wa_2 && pIp_pGyroData_wa_l[3] == pIp_pGyroData_wa_3 && pIp_pGyroData_wa_l[4] == pIp_pGyroData_wa_4 && pIp_pGyroData_wa_l[5] == pIp_pGyroData_wa_5 && pIp_pGyroData_wa_l[6] == pIp_pGyroData_wa_6 && pIp_pGyroData_wa_l[7] == pIp_pGyroData_wa_7 && pIp_pGyroData_wa_l[8] == pIp_pGyroData_wa_8 && store_int_array(pIp->pGyroData->wal,9, pIp_pGyroData_wal_l) && pIp_pGyroData_wal_l[0] == pIp_pGyroData_wal_0 && pIp_pGyroData_wal_l[1] == pIp_pGyroData_wal_1 && pIp_pGyroData_wal_l[2] == pIp_pGyroData_wal_2 && pIp_pGyroData_wal_l[3] == pIp_pGyroData_wal_3 && pIp_pGyroData_wal_l[4] == pIp_pGyroData_wal_4 && pIp_pGyroData_wal_l[5] == pIp_pGyroData_wal_5 && pIp_pGyroData_wal_l[6] == pIp_pGyroData_wal_6 && pIp_pGyroData_wal_l[7] == pIp_pGyroData_wal_7 && pIp_pGyroData_wal_l[8] == pIp_pGyroData_wal_8 && pIp->pGyroData->JoinTotal == pIp_pGyroData_JoinTotal && pIp->pGyroData->gyroStatus0 == pIp_pGyroData_gyroStatus0 && pIp->pGyroData->gyroStatus1 == pIp_pGyroData_gyroStatus1 && store_int_array(pIp->pGyroData->W,3, pIp_pGyroData_W_l) && pIp_pGyroData_W_l[0] == pIp_pGyroData_W_0 && pIp_pGyroData_W_l[1] == pIp_pGyroData_W_1 && pIp_pGyroData_W_l[2] == pIp_pGyroData_W_2 && store_int_array(pIp->pGyroData->SignFlag,9, pIp_pGyroData_SignFlag_l) && pIp_pGyroData_SignFlag_l[0] == pIp_pGyroData_SignFlag_0 && pIp_pGyroData_SignFlag_l[1] == pIp_pGyroData_SignFlag_1 && pIp_pGyroData_SignFlag_l[2] == pIp_pGyroData_SignFlag_2 && pIp_pGyroData_SignFlag_l[3] == pIp_pGyroData_SignFlag_3 && pIp_pGyroData_SignFlag_l[4] == pIp_pGyroData_SignFlag_4 && pIp_pGyroData_SignFlag_l[5] == pIp_pGyroData_SignFlag_5 && pIp_pGyroData_SignFlag_l[6] == pIp_pGyroData_SignFlag_6 && pIp_pGyroData_SignFlag_l[7] == pIp_pGyroData_SignFlag_7 && pIp_pGyroData_SignFlag_l[8] == pIp_pGyroData_SignFlag_8 && store_int_array(pIp->pGyroData->Rtemp,3, pIp_pGyroData_Rtemp_l) && pIp_pGyroData_Rtemp_l[0] == pIp_pGyroData_Rtemp_0 && pIp_pGyroData_Rtemp_l[1] == pIp_pGyroData_Rtemp_1 && pIp_pGyroData_Rtemp_l[2] == pIp_pGyroData_Rtemp_2 && store_int_array(pIp->pGyroData->stateFlag,9, pIp_pGyroData_stateFlag_l) && pIp_pGyroData_stateFlag_l[0] == pIp_pGyroData_stateFlag_0 && pIp_pGyroData_stateFlag_l[1] == pIp_pGyroData_stateFlag_1 && pIp_pGyroData_stateFlag_l[2] == pIp_pGyroData_stateFlag_2 && pIp_pGyroData_stateFlag_l[3] == pIp_pGyroData_stateFlag_3 && pIp_pGyroData_stateFlag_l[4] == pIp_pGyroData_stateFlag_4 && pIp_pGyroData_stateFlag_l[5] == pIp_pGyroData_stateFlag_5 && pIp_pGyroData_stateFlag_l[6] == pIp_pGyroData_stateFlag_6 && pIp_pGyroData_stateFlag_l[7] == pIp_pGyroData_stateFlag_7 && pIp_pGyroData_stateFlag_l[8] == pIp_pGyroData_stateFlag_8 && store_int_array(pIp->pGyroData->tmpwa,5, pIp_pGyroData_tmpwa_l) && pIp_pGyroData_tmpwa_l[0] == pIp_pGyroData_tmpwa_0 && pIp_pGyroData_tmpwa_l[1] == pIp_pGyroData_tmpwa_1 && pIp_pGyroData_tmpwa_l[2] == pIp_pGyroData_tmpwa_2 && pIp_pGyroData_tmpwa_l[3] == pIp_pGyroData_tmpwa_3 && pIp_pGyroData_tmpwa_l[4] == pIp_pGyroData_tmpwa_4
Ensure emp
*/{

	int i = 0;

	pIp -> pGyroData->JoinTotal = 0 ;
	pIp -> pGyroData->gyroStatus0 = 0 ;

	for (; i<9 ; i++ )
	{
		if (pIp -> pGyroData->stateFlag[i] == 1)
		{
			pIp -> pGyroData->SignFlag[pIp -> pGyroData->JoinTotal] = i ;
			pIp -> pGyroData->JoinTotal++ ;
			pIp -> pGyroData->gyroStatus0 = pIp -> pGyroData->gyroStatus0 | (1 << i) ;
		}

	}

	return ;
}