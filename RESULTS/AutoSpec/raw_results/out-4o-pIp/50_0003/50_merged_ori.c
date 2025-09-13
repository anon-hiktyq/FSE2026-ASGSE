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
requires \valid(pIp- > pGyroData- > wal + (0..8));
requires \valid(pIp- > pGyroData- > wa + (0..8));
requires \valid(pIp- > pGyroData- > countPick + (0..8));
requires \valid(pIp) && \valid(pIp- > pGyroData);
requires \valid(pIp) && \valid(pIp- > pGyroData) &&;
requires \valid(pIp) && \valid(pIp- > pGyroData) && \valid(pIp- > pGyroData- > wa + (0..8)) && \valid(pIp- > pGyroData- > wal + (0..8)) && \valid(pIp- > pGyroData- > countPick + (0..8));
requires \valid(pIp) && \valid(pIp- > pGyroData) && \valid(pIp- > pGyroData- > countPick + (0..8)) && \valid(pIp- > pGyroData- > wa + (0..8)) && \valid(pIp- > pGyroData- > wal + (0..8));
requires \valid(pGyroData) && \valid(pGyroData- > countPick+(0..8)) && \valid(pGyroData- > wa+(0..8)) && \valid(pGyroData- > wal+(0..8));
requires \valid(pGyroData) && \valid(pGyroData- > countPick + (0..8)) && \valid(pGyroData- > wa + (0..8)) && \valid(pGyroData- > wal + (0..8));
pIp- > pGyroData- > wal[i] == pIp- > pGyroData- > wa[i] && pIp- > pGyroData- > countPick[i] == 0);
pIp- > pGyroData- > wal[0..8];
pIp- > pGyroData- > wa[0..8],;
pIp- > pGyroData- > countPick[i] == 0) ||;
pIp- > pGyroData- > countPick[i] < 6);
ensures x >= 0 ==> \result == x;
ensures x < 0 ==> \result == -x;
ensures \forall integer i; 0 <= i < 9 ==> pIp->pGyroData->countPick[i] >= 0;
ensures \forall integer i; 0 <= i < 9 ==> pIp->pGyroData->countPick[i] <= 6;
ensures \forall integer i; 0 <= i < 9 ==> pIp->pGyroData->countPick[i] <= 5;
ensures \forall integer i; 0 <= i < 9 ==> pGyroData->countPick[i] >= 0;
ensures \forall integer i; 0 <= i < 9 ==> (;
ensures \forall integer i; 0 <= i < 9 == >;
assigns pIp- > pGyroData- > wa[0..8], pIp- > pGyroData- > wal[0..8], pIp- > pGyroData- > countPick[0..8];
assigns pIp- > pGyroData- > countPick[0..8],;
assigns pIp- > pGyroData- > countPick[0..8], pIp- > pGyroData- > wa[0..8], pIp- > pGyroData- > wal[0..8];
assigns pGyroData- > countPick[0..8], pGyroData- > wa[0..8], pGyroData- > wal[0..8];
assigns \nothing;
\valid(pIp- > pGyroData- > wal + (0..8));
\valid(pIp- > pGyroData- > wa + (0..8)) &&;
\valid(pIp- > pGyroData- > countPick + (0..8)) &&;
);
(pIp- > pGyroData- > wa[i] == pIp- > pGyroData- > wal[i] &&;
(pIp- > pGyroData- > wa[i] != pIp- > pGyroData- > wal[i] &&;
(pGyroData- > countPick[i] == \old(pGyroData- > countPick[i]) + 1)) &&;
(pGyroData- > countPick[i] == 0 && pGyroData- > wal[i] == pGyroData- > wa[i]));
(pGyroData- > countPick[i] == 0 && pGyroData- > wal[i] == pGyroData- > wa[i]) ||;
(pGyroData- > countPick[i] < 6 && pGyroData- > wa[i] == \old(pGyroData- > wal[i])) ||;
(\old(pGyroData- > wa[i]) == \old(pGyroData- > wal[i]) == >;
(\old(pGyroData- > wa[i]) != \old(pGyroData- > wal[i]) == >;
(ABS(pIp- > pGyroData- > wa[i] - pIp- > pGyroData- > wal[i]) == 0 == >;
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