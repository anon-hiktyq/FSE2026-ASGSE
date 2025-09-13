
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

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


int ABS(int x)
/*@

Require emp
Ensure (x >= 0 && __return == x) || (x < 0 && __return == -x)
*/
{
    if (x < 0)
        return -x;
    else
        return x;
}

void GyroPickFun(GyroPick *pIp)
/*@
With pIp_pGyroData_countPick_l pIp_pGyroData_wa_l pIp_pGyroData_wal_l
Require store_int_array(pIp->pGyroData->countPick,9, pIp_pGyroData_countPick_l) && store_int_array(pIp->pGyroData->wa,9, pIp_pGyroData_wa_l) && store_int_array(pIp->pGyroData->wal,9, pIp_pGyroData_wal_l)
Ensure emp
*/
{

    int iy = 0 ;
    int tmpgi = 0 ;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    exists  pIp_pGyroData_countPick_l pIp_pGyroData_wa_l pIp_pGyroData_wal_l,    
    store_int_array(pIp->pGyroData->countPick, 9, pIp_pGyroData_countPick_l) && store_int_array(pIp->pGyroData->wa, 9, pIp_pGyroData_wa_l) && store_int_array(pIp->pGyroData->wal, 9, pIp_pGyroData_wal_l) &&
    (0 <= iy && iy <= 9) &&
((iy == 0 && tmpgi == 0) || (iy > 0)) &&
(pIp == pIp@pre) &&
(forall (i:Z), iy <= i && i < 9 => (pIp_pGyroData_countPick_l[i] == pIp_pGyroData_countPick_l[i]@pre)) &&
(forall (i:Z), iy <= i && i < 9 => (pIp_pGyroData_wal_l[i] == pIp_pGyroData_wal_l[i]@pre)
      loop assigns iy, tmpgi, pIp_pGyroData_countPick_l[0..8], pIp_pGyroData_wa_l[0..8], pIp_pGyroData_wal_l[0..8])
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
main48(GyroPick *pIp)

/*@
With pIp_pGyroData_countPick_l pIp_pGyroData_wa_l pIp_pGyroData_wal_l
Require store_int_array(pIp->pGyroData->countPick,9, pIp_pGyroData_countPick_l) && store_int_array(pIp->pGyroData->wa,9, pIp_pGyroData_wa_l) && store_int_array(pIp->pGyroData->wal,9, pIp_pGyroData_wal_l)
Ensure Results(__return)
*/{
    pIp -> pGyroData->wa[0] = 1;
    pIp -> pGyroData->wal[0] = 2;
    GyroPickFun(pIp);

    
}