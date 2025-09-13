
typedef struct TAG_DIGITAL_GYRO_DATA
{
    int     countPick[9];        
    int     Gi[3];               
    int     wa[9];               
    int     wal[9];              
    int     JoinTotal;           
    int     gyroStatus0;         
    int     gyroStatus1;         
    int     W[3];                
    int     SignFlag[9];         
    int     Rtemp[3][5];         
    int     stateFlag[9];
    int     tmpwa[5];    

} SGyroData;

typedef struct __CalculateGyroDg
{
    SGyroData*          pGyroData;

} CalculateGyroDg;

void MatrixMulti(SGyroData *pIp)
{
    int ir = 0;
    int jc = 0;
    int nk = 0;
    int index = 0 ;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant 0 <= ir <= 3;
      loop invariant \forall integer i; 0 <= i < ir ==> 
                      (pIp->W[i] == \sum(0, 4, 
                      (\forall integer j; 0 <= j < 5 ==> pIp->Rtemp[i][j] * pIp->tmpwa[j])));
    */
    for (; ir < 3; ir++)
    {
        jc = 0;
        /*@
          loop invariant 0 <= jc <= 1;
          loop invariant index == ir * 1 + jc;
          loop invariant \forall integer i; 0 <= i < 9 ==> 
                          pIp->countPick[i] == \at(pIp->countPick[i],Pre);
          loop invariant \forall integer i; 0 <= i < 3 ==> 
                          pIp->Gi[i] == \at(pIp->Gi[i],Pre);
          loop invariant \forall integer i; 0 <= i < 9 ==> 
                          pIp->wa[i] == \at(pIp->wa[i],Pre);
          loop invariant \forall integer i; 0 <= i < 9 ==> 
                          pIp->wal[i] == \at(pIp->wal[i],Pre);
          loop invariant \forall integer i; 0 <= i < 3 ==> 
                          pIp->W[i] == \at(pIp->W[i],Pre);
          loop invariant \forall integer i; 0 <= i < 9 ==> 
                          pIp->SignFlag[i] == \at(pIp->SignFlag[i],Pre);
          loop invariant \forall integer i, integer j; 0 <= i < 3 && 0 <= j < 5 ==> 
                          pIp->Rtemp[i][j] == \at(pIp->Rtemp[i][j],Pre);
          loop invariant \forall integer i; 0 <= i < 9 ==> 
                          pIp->stateFlag[i] == \at(pIp->stateFlag[i],Pre);
          loop invariant \forall integer i; 0 <= i < 5 ==> 
                          pIp->tmpwa[i] == \at(pIp->tmpwa[i],Pre);
        */
        for (; jc < 1; jc++)
        {
            index = ir * 1 + jc ;
            pIp->W[index] = 0 ;
            nk = 0;
            
            /* >>> LOOP INVARIANT TO FILL <<< */
            /*@
                loop invariant 0 <= nk <= 5;
                loop invariant \forall integer i; 0 <= i < nk ==> 
                                pIp->W[index] == \sum(0, nk-1, 
                                (pIp->Rtemp[ir][i] * pIp->tmpwa[i]));
            */
            for (; nk < 5; nk++)
            {
                pIp->W[index] = pIp->W[index] + 
                                pIp->Rtemp[ir][nk] * pIp->tmpwa[nk];
            }
        }
    }
    return;
}

void CalculateGyroDgFun(CalculateGyroDg *pIp)
{
    int j = 0;
    int k = 0;

    for (; j < 5; j++)
    {
        pIp->tmpwa[j] = 0 ;
    }

    j = 0;

    for (; j < pIp->pGyroData->JoinTotal; j++)
    {
        k = pIp->pGyroData->SignFlag[j];
        pIp->tmpwa[j] = pIp->pGyroData->wa[k];
    }

    if (pIp->pGyroData->JoinTotal >= 3)
    {
        MatrixMulti(pIp);
    }
    else
    {
        pIp->pGyroData->W[0] = 0 ;
        pIp->pGyroData->W[1] = 0 ;
        pIp->pGyroData->W[2] = 0 ;
    }

    return;
}
