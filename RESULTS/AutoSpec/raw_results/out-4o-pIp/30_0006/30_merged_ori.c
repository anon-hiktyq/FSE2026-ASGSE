

typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;


/*@
requires \valid(pIp- > ret);
requires \valid(pIp);
requires \valid(pIp) && \valid(pIp- > ret);
ensures pIp->value >= -pIp->bound;
ensures pIp->value == (pIp->in > pIp->bound ? pIp->bound : (pIp->in < -pIp->bound ? -pIp->bound : pIp->in));
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound;
ensures pIp- > value <= pIp- > bound;
ensures \result == (pIp->in > pIp->bound ? pIp->bound : (pIp->in < -pIp->bound ? -pIp->bound : pIp->in));
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in;
ensures *(pIp- > ret) == pIp- > value;
ensures *(pIp- > ret) == \result;
assigns pIp- > value, *(pIp- > ret);
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


void main30(LimitInt32 *pIp)
{
	pIp -> in = 0;
	pIp -> bound = 0;

	LimitInt32Fun(pIp);

    // @ assert pIp->value == 0;
	// @ assert *(pIp -> ret) == 0;
    // @ assert pIp -> in == 0;
    // @ assert pIp -> bound == 0;
}