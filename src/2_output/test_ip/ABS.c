
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

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