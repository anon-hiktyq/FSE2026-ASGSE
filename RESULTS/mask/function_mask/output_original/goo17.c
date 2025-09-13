
typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;

/*@
requires \valid(pIp);
requires \valid(pIp->ret);
requires pIp->bound >= 0;

assigns pIp->value, *pIp->ret;

ensures \old(pIp->in) >= -\old(pIp->bound) && \old(pIp->in) <= \old(pIp->bound) ==> 
    pIp->value == \old(pIp->in) && *pIp->ret == \old(pIp->in);

ensures \old(pIp->in) < -\old(pIp->bound) ==> 
    pIp->value == -\old(pIp->bound) && *pIp->ret == -\old(pIp->bound);

ensures \old(pIp->in) > \old(pIp->bound) ==> 
    pIp->value == \old(pIp->bound) && *pIp->ret == \old(pIp->bound);
*/

void LimitInt32Fun(LimitInt32 *pIp)
{
    if (pIp -> in > pIp -> bound)
    {
        pIp -> value = pIp -> bound ;
    }
    else if (pIp -> in < -pIp -> bound)
    {
        pIp -> value = -pIp -> bound ;
    }
    else
    {
        pIp -> value = pIp -> in ;
    }

    *(pIp -> ret) = pIp -> value ;
}

/*@
requires \valid(pIp);
requires \valid(pIp->ret);
assigns pIp->in, pIp->bound, pIp->value, *pIp->ret;
*/
void goo17(LimitInt32 *pIp)
{
	pIp -> in = 0;
	pIp -> bound = 0;

	LimitInt32Fun(pIp);

    /* MASK_ACSL_ASSERT */
	/* MASK_ACSL_ASSERT */
}
