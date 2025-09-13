
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    typedef struct __MatrixMulti
{

/* 输入端口 */
	const int*	multiplier;
	int	    nrow;
	int		nrc;
	int		ncol;
	/* 输出端口 */
	/* 输入输出端口 */
	int *	product;
	const int*	faciend;
	/* 状态变量 */
	/* 参数变量 */
} MatrixMulti;

void MatrixMultiFun(MatrixMulti *pIp)

/*@
With pIp_multiplier_v pIp_multiplier pIp_nrow pIp_nrc pIp_ncol pIp_product_v pIp_product pIp_faciend_v pIp_faciend
Require *(pIp->multiplier) == pIp_multiplier_v && (pIp->multiplier) == pIp_multiplier && pIp->nrow == pIp_nrow && pIp->nrc == pIp_nrc && pIp->ncol == pIp_ncol && *(pIp->product) == pIp_product_v && (pIp->product) == pIp_product && *(pIp->faciend) == pIp_faciend_v && (pIp->faciend) == pIp_faciend
Ensure emp
*/{

    int ir =0;
    int jc =0;
    int nk =0;
    int index=0 ;

    for (; ir<pIp -> nrow ; ir++)
    {
        jc = 0;
        for (; jc<pIp -> ncol ; jc++)
        {
            index = ir * pIp -> ncol + jc ;

            pIp -> product[index] = 0 ;

            nk = 0;
            for (; nk<pIp -> nrc ; nk++)
            {
                pIp -> product[index] = pIp -> product[index] + pIp -> faciend[ir * pIp -> nrc + nk] * pIp -> multiplier[nk * pIp -> ncol + jc] ;
            }
        }
    }

    return ;
}