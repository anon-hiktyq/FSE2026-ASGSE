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


typedef struct TAG_DIGITAL_GYRO_DATA
{
    int countPick[9];		 		 	
    int wa[9];				 	
    int wal[9];				 
} SGyroData;

typedef struct __GyroPick
{
    SGyroData* pGyroData;
} GyroPick;

/*@ 
  assigns \nothing;
  ensures \result == (x < 0 ? -x : x);
*/
int ABS(int x)
{
    if (x < 0)
        return -x;
    else
        return x;
}


typedef struct TAG_DIGITAL_GYRO_DATA
{
    int countPick[9];		 		 	
    int wa[9];				 	
    int wal[9];				 
} SGyroData;

typedef struct __GyroPick
{
    SGyroData* pGyroData;
} GyroPick;

/*@
  predicate valid_processed_counts(GyroPick* pIp, integer end) =
    \forall integer i; 0 <= i < end ==> 
      0 <= pIp->pGyroData->countPick[i] <= 5;
*/

/*@ 
  assigns \nothing;
  ensures \result == (x < 0 ? -x : x);
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
    requires \valid(pIp->pGyroData);
    requires \valid(pIp->pGyroData->countPick + (0..8));
    requires \valid(pIp->pGyroData->wa + (0..8));
    requires \valid(pIp->pGyroData->wal + (0..8));
    requires \forall integer i; 0 <= i < 9 ==> 0 <= pIp->pGyroData->countPick[i];
    assigns pIp->pGyroData->countPick[0..8], pIp->pGyroData->wa[0..8], pIp->pGyroData->wal[0..8];
    ensures \forall integer i; 0 <= i < 9 ==> 0 <= pIp->pGyroData->countPick[i] <= 5;
*/
void GyroPickFun(GyroPick *pIp)
{
    int iy = 0 ;
    int tmpgi = 0 ;
    
    /*@
      loop invariant 0 <= iy <= 9;
      loop invariant (iy == 0 && tmpgi == 0) || (iy > 0);
      loop invariant pIp == \at(pIp,Pre);
      loop invariant \forall integer i; iy <= i < 9 ==> (pIp->pGyroData->countPick[i] == \at(pIp->pGyroData->countPick[i], Pre));
      loop invariant \forall integer i; iy <= i < 9 ==> (pIp->pGyroData->wal[i] == \at(pIp->pGyroData->wal[i], Pre));
      loop invariant \forall integer i; 0 <= i < iy ==> 0 <= pIp->pGyroData->countPick[i] <= 5;
      loop assigns iy, tmpgi, pIp->pGyroData->countPick[0..8], pIp->pGyroData->wa[0..8], pIp->pGyroData->wal[0..8];
    */
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

    /*@ assert pIp -> pGyroData->countPick[0] == 1; */
}