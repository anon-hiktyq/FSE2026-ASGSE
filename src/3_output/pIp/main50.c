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
  logic integer abs_logic(integer x) = x < 0 ? -x : x;
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
    ensures \forall integer i; 0 <= i < 9 ==> 
             (abs_logic(\old(pIp->pGyroData->wa[i]) - \old(pIp->pGyroData->wal[i])) == 0) ==> 
             (pIp->pGyroData->wal[i] == pIp->pGyroData->wa[i] && pIp->pGyroData->countPick[i] == 0);
    ensures \forall integer i; 0 <= i < 9 ==> 
             (abs_logic(\old(pIp->pGyroData->wa[i]) - \old(pIp->pGyroData->wal[i])) > 0 && \old(pIp->pGyroData->countPick[i]) < 5) ==> 
             (pIp->pGyroData->wa[i] == \old(pIp->pGyroData->wal[i]) && pIp->pGyroData->countPick[i] == \old(pIp->pGyroData->countPick[i]) + 1);
    ensures \forall integer i; 0 <= i < 9 ==> 
             (abs_logic(\old(pIp->pGyroData->wa[i]) - \old(pIp->pGyroData->wal[i])) > 0 && \old(pIp->pGyroData->countPick[i]) >= 5) ==> 
             (pIp->pGyroData->wal[i] == \old(pIp->pGyroData->wa[i]) && pIp->pGyroData->countPick[i] == 0);
*/
void GyroPickFun(GyroPick *pIp)
{
    int iy = 0;
    int tmpgi = 0;
    
    /*@
      loop invariant 0 <= iy <= 9;
      loop invariant pIp == \at(pIp, Pre);
      loop invariant \forall integer i; iy <= i < 9 ==> pIp->pGyroData->wal[i] == \at(pIp->pGyroData->wal[i], Pre);
      loop invariant \forall integer i; iy <= i < 9 ==> pIp->pGyroData->wa[i] == \at(pIp->pGyroData->wa[i], Pre);
      loop assigns iy, tmpgi, pIp->pGyroData->countPick[0..8], pIp->pGyroData->wa[0..8], pIp->pGyroData->wal[0..8];
    */
    for (; iy < 9 ; iy++)
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
    
main50(GyroPick *pIp)
{
    pIp -> pGyroData->wa[0] = 1;
    pIp -> pGyroData->wal[0] = 2;
    pIp -> pGyroData->countPick[0] = 10;
    GyroPickFun(pIp);

    /*@ assert pIp -> pGyroData->countPick[0] == 0; */
    /*@ assert pIp -> pGyroData->wal[0] == pIp -> pGyroData->wa[0]; */
}