typedef struct TAG_DIGITAL_GYRO_DATA
{

    int		countPick[9];		 	 	
    int 	wa[9];				 	
    int 	wal[9];				 
	
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

/*@
requires \valid(pGyroData) && \valid(pGyroData->countPick+(0..8)) && \valid(pGyroData->wa+(0..8)) && \valid(pGyroData->wal+(0..8));
ensures \forall integer i; 0 <= i < 9 ==> 
    (\old(pGyroData->wa[i]) != \old(pGyroData->wal[i]) ==> 
        (pGyroData->countPick[i] == 0 && pGyroData->wal[i] == pGyroData->wa[i]) || 
        (pGyroData->countPick[i] < 6 && pGyroData->wa[i] == \old(pGyroData->wal[i])) ||
        (pGyroData->countPick[i] == \old(pGyroData->countPick[i]) + 1)) &&
    (\old(pGyroData->wa[i]) == \old(pGyroData->wal[i]) ==> 
        (pGyroData->countPick[i] == 0 && pGyroData->wal[i] == pGyroData->wa[i]));
assigns pGyroData->countPick[0..8], pGyroData->wa[0..8], pGyroData->wal[0..8];
*/
int ABS(int x)
{
    if (x < 0)
        return -x;
    else
        return x;
}

/*@
requires \valid(pIp);
*/
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

/*@
requires \valid(pIp);
*/
main50(GyroPick *pIp)
{
    pIp -> pGyroData->wa[0] = 1;
    pIp -> pGyroData->wal[0] = 2;
    pIp -> pGyroData->countPick[0] = 10;
    GyroPickFun(pIp);

    // @ assert pIp -> pGyroData->countPick[0] == 0;
    // @ assert pIp -> pGyroData->wal[0] == pIp -> pGyroData->wa[0];
}