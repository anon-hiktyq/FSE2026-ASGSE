
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
{

	int i = 0;

	pIp -> pGyroData->JoinTotal = 0 ;
	pIp -> pGyroData->gyroStatus0 = 0 ;

	
            
            /*@
          loop invariant 0 <= i <= 9;
          loop invariant pIp == \at(pIp,Pre);
            */
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
