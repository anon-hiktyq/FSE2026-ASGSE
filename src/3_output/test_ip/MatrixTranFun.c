
typedef struct __MatrixTran
{
    const int*   mat;
    int          nrow;
    int          ncol;
    int*         tran;
} MatrixTran;

void MatrixTranFun(MatrixTran *pIp)
{
    int i = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
        (\forall int j; 0 <= j < \at(pIp,Pre)->ncol ==> 
          *(pIp->tran + j * \at(pIp,Pre)->nrow + k) == *(pIp->mat + k * \at(pIp,Pre)->ncol + j)));
      loop invariant pIp == \at(pIp,Pre);
    */
    for (; i < pIp->nrow; i++)
    {
        int j = 0;
        /*@
            *(pIp->tran + k * pIp->nrow + i) == *(pIp->mat + i * pIp->ncol + k);
        */
        for (; j < pIp->ncol; j++)
        {
            *(pIp->tran + j * pIp->nrow + i) = *(pIp->mat + i * pIp->ncol + j);
        }
    }

    return;
}
