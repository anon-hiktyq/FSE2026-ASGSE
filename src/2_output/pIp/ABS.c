
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