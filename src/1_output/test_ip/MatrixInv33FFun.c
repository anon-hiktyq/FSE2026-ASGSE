
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    typedef struct __MatrixInv33F
{

/* 输入端口 */
	const int src[9]; 
	/* 输出端口 */
	int		bAbleInv;
	int		ret;
	/* 输入输出端口 */
	int		inv[9];
	/* 状态变量 */
	/* 参数变量 */
} MatrixInv33F;

void MatrixInv33FFun(MatrixInv33F *pIp)

/*@
With pIp_src_l pIp_src_0 pIp_src_1 pIp_src_2 pIp_src_3 pIp_src_4 pIp_src_5 pIp_src_6 pIp_src_7 pIp_src_8 pIp_bAbleInv pIp_ret pIp_inv_l pIp_inv_0 pIp_inv_1 pIp_inv_2 pIp_inv_3 pIp_inv_4 pIp_inv_5 pIp_inv_6 pIp_inv_7 pIp_inv_8
Require store_int_array(pIp->src,9, pIp_src_l) && pIp_src_l[0] == pIp_src_0 && pIp_src_l[1] == pIp_src_1 && pIp_src_l[2] == pIp_src_2 && pIp_src_l[3] == pIp_src_3 && pIp_src_l[4] == pIp_src_4 && pIp_src_l[5] == pIp_src_5 && pIp_src_l[6] == pIp_src_6 && pIp_src_l[7] == pIp_src_7 && pIp_src_l[8] == pIp_src_8 && pIp->bAbleInv == pIp_bAbleInv && pIp->ret == pIp_ret && store_int_array(pIp->inv,9, pIp_inv_l) && pIp_inv_l[0] == pIp_inv_0 && pIp_inv_l[1] == pIp_inv_1 && pIp_inv_l[2] == pIp_inv_2 && pIp_inv_l[3] == pIp_inv_3 && pIp_inv_l[4] == pIp_inv_4 && pIp_inv_l[5] == pIp_inv_5 && pIp_inv_l[6] == pIp_inv_6 && pIp_inv_l[7] == pIp_inv_7 && pIp_inv_l[8] == pIp_inv_8
Ensure emp
*/{

    int i;
    int rank;

    pIp -> bAbleInv = 0;

    pIp -> inv[0] = pIp -> src[4] * pIp -> src[8] - pIp -> src[5] * pIp -> src[7];
    pIp -> inv[1] = pIp -> src[2] * pIp -> src[7] - pIp -> src[1] * pIp -> src[8];
    pIp -> inv[2] = pIp -> src[1] * pIp -> src[5] - pIp -> src[2] * pIp -> src[4];
    pIp -> inv[3] = pIp -> src[5] * pIp -> src[6] - pIp -> src[3] * pIp -> src[8];
    pIp -> inv[4] = pIp -> src[0] * pIp -> src[8] - pIp -> src[2] * pIp -> src[6];
    pIp -> inv[5] = pIp -> src[2] * pIp -> src[3] - pIp -> src[0] * pIp -> src[5];
    pIp -> inv[6] = pIp -> src[3] * pIp -> src[7] - pIp -> src[4] * pIp -> src[6];
    pIp -> inv[7] = pIp -> src[1] * pIp -> src[6] - pIp -> src[0] * pIp -> src[7];
    pIp -> inv[8] = pIp -> src[0] * pIp -> src[4] - pIp -> src[1] * pIp -> src[3];

    rank = pIp -> src[0] * pIp -> inv[0] + pIp -> src[1] * pIp -> inv[3] + pIp -> src[2] * pIp -> inv[6];

    if ((FLT32_ZERO < rank) || (rank < -FLT32_ZERO))
    {

        pIp -> bAbleInv = 1;

        for (i=0; i<9; i++)
        {
            pIp -> inv[i] = pIp -> inv[i] / rank;
        }
    }
    else
    {

        for (i=0; i<9; i++)
        {
            pIp -> inv[i] = pIp -> src[i];
        }
    }

    *(pIp -> ret) = pIp -> bAbleInv;
}