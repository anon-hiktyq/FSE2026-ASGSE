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
requires INT_MIN < x <= INT_MAX;
ensures x >= 0 ==> \result == x;
ensures x < 0 ==> \result == -x;
ensures \result >= 0;
assigns \nothing;
```c;
```;
Looking at the context and the function ABS, I need to generate ACSL function contract annotations.;
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