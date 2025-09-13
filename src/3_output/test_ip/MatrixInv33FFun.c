
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
{
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

    if ((0.0001 < rank) || (rank < -0.0001))
    {
        pIp -> bAbleInv = 1;

        /*@
        loop invariant 0 <= i <= 9;
            (pIp->inv[j] == (pIp->src[4] * pIp->src[8] - pIp->src[5] * pIp->src[7]) / rank ||
             pIp->inv[j] == (pIp->src[2] * pIp->src[7] - pIp->src[1] * pIp->src[8]) / rank ||
             pIp->inv[j] == (pIp->src[1] * pIp->src[5] - pIp->src[2] * pIp->src[4]) / rank ||
             pIp->inv[j] == (pIp->src[5] * pIp->src[6] - pIp->src[3] * pIp->src[8]) / rank ||
             pIp->inv[j] == (pIp->src[0] * pIp->src[8] - pIp->src[2] * pIp->src[6]) / rank ||
             pIp->inv[j] == (pIp->src[2] * pIp->src[3] - pIp->src[0] * pIp->src[5]) / rank ||
             pIp->inv[j] == (pIp->src[3] * pIp->src[7] - pIp->src[4] * pIp->src[6]) / rank ||
             pIp->inv[j] == (pIp->src[1] * pIp->src[6] - pIp->src[0] * pIp->src[7]) / rank ||
             pIp->inv[j] == (pIp->src[0] * pIp->src[4] - pIp->src[1] * pIp->src[3]) / rank);
        */
        for (i=0; i<9; i++)
        {
            pIp -> inv[i] = pIp -> inv[i] / rank;
        }
    }
    else
    {
        /*@
        loop invariant 0 <= i <= 9;
        */
        for (i=0; i<9; i++)
        {
            pIp -> inv[i] = pIp -> src[i];
        }
    }

    pIp -> ret = pIp -> bAbleInv;
}
