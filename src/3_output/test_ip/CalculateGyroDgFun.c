
typedef struct TAG_DIGITAL_GYRO_DATA
{
    int countPick[9];		 
    int Gi[3];				 	
    int wa[9];				 	
    int wal[9];				 
    int JoinTotal;           	
    int gyroStatus0;		 	
    int gyroStatus1;		 
    int W[3];				 	
    int SignFlag[9]; 		 	 
    int Rtemp[3][5];		 	
    int stateFlag[9];
    int tmpwa[5];	
} SGyroData;

typedef struct __CalculateGyroDg
{
    SGyroData* pGyroData;
} CalculateGyroDg;

void MatrixMulti(SGyroData *pIp)
{
    int ir = 0;
    int jc = 0;
    int nk = 0;
    int index = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant pIp->tmpwa[0] == \at(pIp->tmpwa[0], Pre) && pIp->tmpwa[1] == \at(pIp->tmpwa[1], Pre) && pIp->tmpwa[2] == \at(pIp->tmpwa[2], Pre) && pIp->tmpwa[3] == \at(pIp->tmpwa[3], Pre) && pIp->tmpwa[4] == \at(pIp->tmpwa[4], Pre);
      loop invariant pIp->stateFlag[0] == \at(pIp->stateFlag[0], Pre) && pIp->stateFlag[1] == \at(pIp->stateFlag[1], Pre) && pIp->stateFlag[2] == \at(pIp->stateFlag[2], Pre) && pIp->stateFlag[3] == \at(pIp->stateFlag[3], Pre) && pIp->stateFlag[4] == \at(pIp->stateFlag[4], Pre) && pIp->stateFlag[5] == \at(pIp->stateFlag[5], Pre) && pIp->stateFlag[6] == \at(pIp->stateFlag[6], Pre) && pIp->stateFlag[7] == \at(pIp->stateFlag[7], Pre) && pIp->stateFlag[8] == \at(pIp->stateFlag[8], Pre);
      loop invariant pIp->Rtemp[0][0] == \at(pIp->Rtemp[0][0], Pre) && pIp->Rtemp[1][0] == \at(pIp->Rtemp[1][0], Pre) && pIp->Rtemp[2][0] == \at(pIp->Rtemp[2][0], Pre);
      loop invariant pIp->SignFlag[0] == \at(pIp->SignFlag[0], Pre) && pIp->SignFlag[1] == \at(pIp->SignFlag[1], Pre) && pIp->SignFlag[2] == \at(pIp->SignFlag[2], Pre) && pIp->SignFlag[3] == \at(pIp->SignFlag[3], Pre) && pIp->SignFlag[4] == \at(pIp->SignFlag[4], Pre) && pIp->SignFlag[5] == \at(pIp->SignFlag[5], Pre) && pIp->SignFlag[6] == \at(pIp->SignFlag[6], Pre) && pIp->SignFlag[7] == \at(pIp->SignFlag[7], Pre) && pIp->SignFlag[8] == \at(pIp->SignFlag[8], Pre);
      loop invariant pIp->W[0] == \at(pIp->W[0], Pre) && pIp->W[1] == \at(pIp->W[1], Pre) && pIp->W[2] == \at(pIp->W[2], Pre);
      loop invariant pIp->wal[0] == \at(pIp->wal[0], Pre) && pIp->wal[1] == \at(pIp->wal[1], Pre) && pIp->wal[2] == \at(pIp->wal[2], Pre) && pIp->wal[3] == \at(pIp->wal[3], Pre) && pIp->wal[4] == \at(pIp->wal[4], Pre) && pIp->wal[5] == \at(pIp->wal[5], Pre) && pIp->wal[6] == \at(pIp->wal[6], Pre) && pIp->wal[7] == \at(pIp->wal[7], Pre) && pIp->wal[8] == \at(pIp->wal[8], Pre);
      loop invariant pIp->wa[0] == \at(pIp->wa[0], Pre) && pIp->wa[1] == \at(pIp->wa[1], Pre) && pIp->wa[2] == \at(pIp->wa[2], Pre) && pIp->wa[3] == \at(pIp->wa[3], Pre) && pIp->wa[4] == \at(pIp->wa[4], Pre) && pIp->wa[5] == \at(pIp->wa[5], Pre) && pIp->wa[6] == \at(pIp->wa[6], Pre) && pIp->wa[7] == \at(pIp->wa[7], Pre) && pIp->wa[8] == \at(pIp->wa[8], Pre);
      loop invariant pIp->Gi[0] == \at(pIp->Gi[0], Pre) && pIp->Gi[1] == \at(pIp->Gi[1], Pre) && pIp->Gi[2] == \at(pIp->Gi[2], Pre);
      loop invariant pIp->countPick[0] == \at(pIp->countPick[0], Pre) && pIp->countPick[1] == \at(pIp->countPick[1], Pre) && pIp->countPick[2] == \at(pIp->countPick[2], Pre) && pIp->countPick[3] == \at(pIp->countPick[3], Pre) && pIp->countPick[4] == \at(pIp->countPick[4], Pre) && pIp->countPick[5] == \at(pIp->countPick[5], Pre) && pIp->countPick[6] == \at(pIp->countPick[6], Pre) && pIp->countPick[7] == \at(pIp->countPick[7], Pre) && pIp->countPick[8] == \at(pIp->countPick[8], Pre);
      loop invariant 0 <= ir < 3;
      loop invariant ((index == 0) && (nk == 0) && (jc == 0) && (ir == 0) && (pIp == \at(pIp, Pre)) && (\at(pIp, Pre)->JoinTotal == \at(pIp->JoinTotal, Pre)) && (\at(pIp, Pre)->gyroStatus0 == \at(pIp->gyroStatus0, Pre)) && (\at(pIp, Pre)->gyroStatus1 == \at(pIp->gyroStatus1, Pre))) || (0 <= jc <= 1);
      loop invariant ((index == 0) && (nk == 0) && (jc == 0) && (ir == 0) && (pIp == \at(pIp, Pre)) && (\at(pIp, Pre)->JoinTotal == \at(pIp->JoinTotal, Pre)) && (\at(pIp, Pre)->gyroStatus0 == \at(pIp->gyroStatus0, Pre)) && (\at(pIp, Pre)->gyroStatus1 == \at(pIp->gyroStatus1, Pre))) || (0 <= nk <= 5);
      loop invariant ((index == 0) && (nk == 0) && (jc == 0) && (ir == 0) && (pIp == \at(pIp, Pre)) && (\at(pIp, Pre)->JoinTotal == \at(pIp->JoinTotal, Pre)) && (\at(pIp, Pre)->gyroStatus0 == \at(pIp->gyroStatus0, Pre)) && (\at(pIp, Pre)->gyroStatus1 == \at(pIp->gyroStatus1, Pre))) || (index == ir * 1 + jc);
      loop invariant pIp == \at(pIp, Pre);
      loop invariant \at(pIp, Pre)->JoinTotal == \at(pIp->JoinTotal, Pre);
      loop invariant \at(pIp, Pre)->gyroStatus0 == \at(pIp->gyroStatus0, Pre);
      loop invariant \at(pIp, Pre)->gyroStatus1 == \at(pIp->gyroStatus1, Pre);
    */
    for (; ir < 3; ir++)
    {
        jc = 0;
        
        /*@
          loop invariant 0 <= jc <= 1;
          loop invariant 0 <= ir < 3;
          loop invariant \forall integer i; 0 <= i < jc ==> pIp->W[ir * 1 + i] == (\sum m; 0 <= m < 5; pIp->Rtemp[ir][m] * pIp->tmpwa[m]);
        */
        for (; jc < 1; jc++)
        {
            index = ir * 1 + jc;
            pIp->W[index] = 0;

            nk = 0;

            /*@
              loop invariant 0 <= nk <= 5;
              loop invariant pIp->W[index] == (\sum i; 0 <= i < nk; pIp->Rtemp[ir][i] * pIp->tmpwa[i]);
            */
            for (; nk < 5; nk++)
            {
                pIp->W[index] = pIp->W[index] + pIp->Rtemp[ir][nk] * pIp->tmpwa[nk];
            }
        }
    }
    
    return;
}

void CalculateGyroDgFun(CalculateGyroDg *pIp)
{
    int j = 0;
    int k = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant pIp->tmpwa[0] == 0 && pIp->tmpwa[1] == 0 && pIp->tmpwa[2] == 0 && pIp->tmpwa[3] == 0 && pIp->tmpwa[4] == 0;
      loop invariant 0 <= j <= 5;
      loop invariant (!(j < 5)) ==> ((index == 0)&&(nk == 0)&&(jc == 0)&&(ir == 0)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->JoinTotal == \at(pIp->JoinTotal, Pre))&&(\at(pIp,Pre)->gyroStatus0 == \at(pIp->gyroStatus0, Pre))&&(\at(pIp,Pre)->gyroStatus1 == \at(pIp->gyroStatus1, Pre)));
      loop invariant index == 0;
      loop invariant nk == 0;
      loop invariant jc == 0;
      loop invariant ir == 0;
      loop invariant pIp == \at(pIp, Pre);
      loop invariant \at(pIp, Pre)->JoinTotal == \at(pIp->JoinTotal, Pre);
      loop invariant \at(pIp, Pre)->gyroStatus0 == \at(pIp->gyroStatus0, Pre);
      loop invariant \at(pIp, Pre)->gyroStatus1 == \at(pIp->gyroStatus1, Pre);
    */
    for (; j < 5; j++)
    {
        pIp->tmpwa[j] = 0;
    }

    j = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant 0 <= j <= \at(pIp->JoinTotal, Pre);
      loop invariant \forall integer i; 0 <= i < j ==> pIp->tmpwa[i] == \at(pIp->wa[\at(pIp->SignFlag[i], Pre)], Pre);
    */
    for (; j < pIp->pGyroData->JoinTotal; j++)
    {
        k = pIp->pGyroData->SignFlag[j];
        pIp->tmpwa[j] = pIp->pGyroData->wa[k];
    }

    if (pIp->pGyroData->JoinTotal >= 3)
    {
        MatrixMulti(pIp->pGyroData);
    }
    else
    {
        pIp->pGyroData->W[0] = 0;
        pIp->pGyroData->W[1] = 0;
        pIp->pGyroData->W[2] = 0;
    }

    return;
}
