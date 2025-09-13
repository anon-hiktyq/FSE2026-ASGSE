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
  ensures (x >= 0 ==> \result == x) && (x < 0 ==> \result == -x);
  ensures \result >= 0;
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
    int		countPick[9];		 		 	
    int 	wa[9];				 	
    int 	wal[9];				 
} SGyroData;

typedef struct __GyroPick
{
    SGyroData*			pGyroData;
} GyroPick;

/*@ 
  assigns \nothing;
  ensures (x >= 0 ==> \result == x) && (x < 0 ==> \result == -x);
  ensures \result >= 0;
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
    requires \forall integer i; 0 <= i < 9 ==> pIp->pGyroData->countPick[i] >= 0;
    ensures \forall integer i; 0 <= i < 9 ==> pIp->pGyroData->countPick[i] >= 0;
    ensures \forall integer i; 0 <= i < 9 ==> pIp->pGyroData->countPick[i] <= 6;
    assigns pIp->pGyroData->countPick[0..8], pIp->pGyroData->wa[0..8], pIp->pGyroData->wal[0..8];
*/
void GyroPickFun(GyroPick *pIp)
{
    int iy = 0;
    int tmpgi = 0;
            
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant 0 <= iy <= 9;
      loop invariant ((tmpgi == 0 && iy == 0) || (tmpgi >= 0 && iy > 0));
      loop invariant pIp == \at(pIp, Pre);
      loop invariant \valid(pIp->pGyroData);
      loop invariant \forall integer i; iy <= i < 9 ==> pIp->pGyroData->wal[i] == \at(pIp->pGyroData->wal[i], Pre);
      loop invariant \forall integer i; iy <= i < 9 ==> pIp->pGyroData->wa[i] == \at(pIp->pGyroData->wa[i], Pre);
      loop invariant \forall integer i; 0 <= i < iy ==> pIp->pGyroData->countPick[i] >= 0;
      loop invariant \forall integer i; 0 <= i < iy ==> pIp->pGyroData->countPick[i] <= 6;
      loop assigns iy, tmpgi, pIp->pGyroData->countPick[0..8], pIp->pGyroData->wa[0..8], pIp->pGyroData->wal[0..8];
    */
    for (; iy < 9; iy++)
    {
        tmpgi = ABS(pIp->pGyroData->wa[iy] - pIp->pGyroData->wal[iy]);

        if (tmpgi > 0)
        {
            pIp->pGyroData->countPick[iy]++;

            if (pIp->pGyroData->countPick[iy] < 6)
            {
                pIp->pGyroData->wa[iy] = pIp->pGyroData->wal[iy];
            }
            else
            {
                pIp->pGyroData->wal[iy] = pIp->pGyroData->wa[iy];
                pIp->pGyroData->countPick[iy] = 0;
            }
        }
        else
        {
            pIp->pGyroData->wal[iy] = pIp->pGyroData->wa[iy];
            pIp->pGyroData->countPick[iy] = 0;
        }
    }
    return;
}
/*@
    requires \valid(pIp);
    */
    
main49(GyroPick *pIp)
{
    pIp -> pGyroData->wa[0] = 0;
    pIp -> pGyroData->wal[0] = 0;
    GyroPickFun(pIp);

    /*@ assert pIp -> pGyroData->countPick[0] == 0; */
    /*@ assert pIp -> pGyroData->wal[0] == pIp -> pGyroData->wa[0]; */
}