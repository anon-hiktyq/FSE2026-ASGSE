typedef struct TAG_DIGITAL_GYRO_DATA
{

    int		countPick[9];		 		 	
    int 	wa[9];				 	
    int 	wal[9];				 
	
} SGyroData;

typedef struct __GyroPick
{
	SGyroData*			pGyroData;
	
} GyroPick;

/*@
requires \valid(pIp->pGyroData->wa + (0..8));
requires \valid(pIp->pGyroData->wal + (0..8));
requires \valid(pIp->pGyroData->countPick + (0..8));
assigns pIp->pGyroData->countPick[0..8], pIp->pGyroData->wa[0..8], pIp->pGyroData->wal[0..8];
ensures \forall integer i; 0 <= i < 9 ==> ABS(pIp->pGyroData->wa[i] - pIp->pGyroData->wal[i]) == 0;
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
main48(GyroPick *pIp)
{
    pIp -> pGyroData->wa[0] = 1;
    pIp -> pGyroData->wal[0] = 2;
    GyroPickFun(pIp);

    // @ assert pIp -> pGyroData->countPick[0] == 1;
}