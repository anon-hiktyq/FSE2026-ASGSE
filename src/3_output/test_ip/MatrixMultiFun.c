
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
{

    int ir =0;
    int jc =0;
    int nk =0;
    int index=0 ;

    
            
            /*@
          loop invariant (0<\at(pIp,Pre) -> nrow) ==> (0 <= ir <= \at(pIp,Pre)->nrow) ;
          loop invariant (0<\at(pIp,Pre) -> nrow) ==> (((index == ir * \at(pIp,Pre)->ncol + jc)&&(0 <= nk <= \at(pIp,Pre)->nrc)&&(0 <= jc <= \at(pIp,Pre)->ncol)&&(0 <= ir <= \at(pIp,Pre)->nrow)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->multiplier == \at(pIp->multiplier,Pre))&&(*\at(pIp->multiplier,Pre) == \at(*pIp->multiplier,Pre))&&(\at(pIp,Pre)->nrow == \at(pIp->nrow,Pre))&&(\at(pIp,Pre)->nrc == \at(pIp->nrc,Pre))&&(\at(pIp,Pre)->ncol == \at(pIp->ncol,Pre))&&(\at(pIp,Pre)->product == \at(pIp->product,Pre))&&(*\at(pIp->product,Pre) == \at(*pIp->product,Pre))&&(\at(pIp,Pre)->faciend == \at(pIp->faciend,Pre))&&(*\at(pIp->faciend,Pre) == \at(*pIp->faciend,Pre))) || (0 <= jc <= \at(pIp,Pre)->ncol));
          loop invariant (0<\at(pIp,Pre) -> nrow) ==> (((index == ir * \at(pIp,Pre)->ncol + jc)&&(0 <= nk <= \at(pIp,Pre)->nrc)&&(0 <= jc <= \at(pIp,Pre)->ncol)&&(0 <= ir <= \at(pIp,Pre)->nrow)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->multiplier == \at(pIp->multiplier,Pre))&&(*\at(pIp->multiplier,Pre) == \at(*pIp->multiplier,Pre))&&(\at(pIp,Pre)->nrow == \at(pIp->nrow,Pre))&&(\at(pIp,Pre)->nrc == \at(pIp->nrc,Pre))&&(\at(pIp,Pre)->ncol == \at(pIp->ncol,Pre))&&(\at(pIp,Pre)->product == \at(pIp->product,Pre))&&(*\at(pIp->product,Pre) == \at(*pIp->product,Pre))&&(\at(pIp,Pre)->faciend == \at(pIp->faciend,Pre))&&(*\at(pIp->faciend,Pre) == \at(*pIp->faciend,Pre))) || (0 <= nk <= \at(pIp,Pre)->nrc));
          loop invariant (0<\at(pIp,Pre) -> nrow) ==> (((index == ir * \at(pIp,Pre)->ncol + jc)&&(0 <= nk <= \at(pIp,Pre)->nrc)&&(0 <= jc <= \at(pIp,Pre)->ncol)&&(0 <= ir <= \at(pIp,Pre)->nrow)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->multiplier == \at(pIp->multiplier,Pre))&&(*\at(pIp->multiplier,Pre) == \at(*pIp->multiplier,Pre))&&(\at(pIp,Pre)->nrow == \at(pIp->nrow,Pre))&&(\at(pIp,Pre)->nrc == \at(pIp->nrc,Pre))&&(\at(pIp,Pre)->ncol == \at(pIp->ncol,Pre))&&(\at(pIp,Pre)->product == \at(pIp->product,Pre))&&(*\at(pIp->product,Pre) == \at(*pIp->product,Pre))&&(\at(pIp,Pre)->faciend == \at(pIp->faciend,Pre))&&(*\at(pIp->faciend,Pre) == \at(*pIp->faciend,Pre))) || (index == ir * \at(pIp,Pre)->ncol + jc));
          loop invariant (!(0<\at(pIp,Pre) -> nrow)) ==> ((index == 0)&&(nk == 0)&&(jc == 0)&&(ir == 0)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->multiplier == \at(pIp->multiplier,Pre))&&(*\at(pIp->multiplier,Pre) == \at(*pIp->multiplier,Pre))&&(\at(pIp,Pre)->nrow == \at(pIp->nrow,Pre))&&(\at(pIp,Pre)->nrc == \at(pIp->nrc,Pre))&&(\at(pIp,Pre)->ncol == \at(pIp->ncol,Pre))&&(\at(pIp,Pre)->product == \at(pIp->product,Pre))&&(*\at(pIp->product,Pre) == \at(*pIp->product,Pre))&&(\at(pIp,Pre)->faciend == \at(pIp->faciend,Pre))&&(*\at(pIp->faciend,Pre) == \at(*pIp->faciend,Pre)));
          loop invariant pIp == \at(pIp,Pre);
          loop invariant \at(pIp,Pre)->multiplier == \at(pIp->multiplier,Pre);
          loop invariant *\at(pIp->multiplier,Pre) == \at(*pIp->multiplier,Pre);
          loop invariant \at(pIp,Pre)->nrow == \at(pIp->nrow,Pre);
          loop invariant \at(pIp,Pre)->nrc == \at(pIp->nrc,Pre);
          loop invariant \at(pIp,Pre)->ncol == \at(pIp->ncol,Pre);
          loop invariant \at(pIp,Pre)->product == \at(pIp->product,Pre);
          loop invariant *\at(pIp->product,Pre) == \at(*pIp->product,Pre);
          loop invariant \at(pIp,Pre)->faciend == \at(pIp->faciend,Pre);
          loop invariant *\at(pIp->faciend,Pre) == \at(*pIp->faciend,Pre);
            */
            for (; ir<pIp -> nrow ; ir++)
    {
        jc = 0;
        
        /*@
          loop invariant 0 <= ir <= pIp->nrow;
          loop invariant 0 <= jc <= pIp->ncol;
          loop invariant index == ir * pIp->ncol + jc;
        */
        for (; jc<pIp -> ncol ; jc++)
        {
            index = ir * pIp -> ncol + jc ;

            pIp -> product[index] = 0 ;

            nk = 0;
            
            /* >>> LOOP INVARIANT TO FILL <<< */
            
            /*@
              loop invariant 0 <= nk <= pIp->nrc;
              loop invariant pIp->product[index] == 
                \sum(int k; 0 <= k < nk, 
                pIp->faciend[ir * pIp->nrc + k] * pIp->multiplier[k * pIp->ncol + jc]);
            */
            for (; nk<pIp -> nrc ; nk++)
            {
                pIp -> product[index] = pIp -> product[index] + pIp -> faciend[ir * pIp -> nrc + nk] * pIp -> multiplier[nk * pIp -> ncol + jc] ;
            }
            
        }
            
    }
            

    return ;
}
