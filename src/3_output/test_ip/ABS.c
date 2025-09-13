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

typedef struct __GyroPick
{
    /* 输入端口 */
	/* 输出端口 */
	/* 输入输出端口 */
	SGyroData*			pGyroData;
	/* 状态变量 */
	/* 参数变量 */
} GyroPick;

int ABS(int x)
{
    if (x < 0)
        return -x;
    else
        return x;
}

void GyroPickFun(GyroPick *pIp)
{

    int iy = 0 ;
    int tmpgi = 0 ;

    for (; iy < 9 ; iy++ )
    {

        tmpgi = ABS(pIp -> pGyroData->wa[iy] - pIp -> pGyroData->wal[iy]) ;

        if (tmpgi > 0)
        {
            pIp -> pGyroData->countPick[iy]++ ;

            if (pIp -> pGyroData->countPick[iy] < 6)
            {
                pIp -> pGyroData->wa[iy] = pIp -> pGyroData->wal[iy] ;

            }
            else
            {
                pIp -> pGyroData->wal[iy] = pIp -> pGyroData->wa[iy] ;

                pIp -> pGyroData->countPick[iy] = 0 ;

            }
        }
        else
        {
            pIp -> pGyroData->wal[iy] = pIp -> pGyroData->wa[iy] ;

            pIp -> pGyroData->countPick[iy] = 0 ;

        }
    }

    return ;

}