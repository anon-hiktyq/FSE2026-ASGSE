

typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;


/*@
requires pIp->bound >= 0;
requires \valid(pIp- > ret);
requires \valid(pIp);
requires \valid(pIp) && \valid(pIp- > ret);;
requires \valid(pIp) && \valid(pIp- > ret);
ensures pIp->value >= -pIp->bound;;
ensures pIp->value == pIp->in ==> pIp->in >= -pIp->bound && pIp->in <= pIp->bound;
ensures pIp->value == pIp->bound ==> pIp->in > pIp->bound;
ensures pIp->value == pIp->bound ==> *(pIp->ret) == pIp->bound;
ensures pIp->value == \old(pIp->in) ==> *(pIp->ret) == \old(pIp->in);
ensures pIp->value == -pIp->bound ==> pIp->in < -pIp->bound;
ensures pIp->value == -pIp->bound ==> *(pIp->ret) == -pIp->bound;
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound;
ensures pIp- > value == pIp- > in || pIp- > value == pIp- > bound || pIp- > value == -pIp- > bound;
ensures pIp- > value == \old(pIp- > in) || pIp- > value == pIp- > bound || pIp- > value == -pIp- > bound;
ensures pIp- > value == *(pIp- > ret);
ensures pIp- > value <= pIp- > bound;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in;
ensures *(pIp- > ret) == pIp- > value;
ensures (pIp->in >= -pIp->bound && pIp->in <= pIp->bound) ==> (pIp->value == pIp->in);
ensures (pIp->in > pIp->bound) ==> (pIp->value == pIp->bound);
ensures (pIp->in > pIp->bound) ==> (pIp->value == pIp->bound && *(pIp->ret) == pIp->bound);
ensures (pIp->in < -pIp->bound) ==> (pIp->value == -pIp->bound);
ensures (pIp->in < -pIp->bound) ==> (pIp->value == -pIp->bound && *(pIp->ret) == -pIp->bound);
ensures (-pIp->bound <= pIp->in <= pIp->bound) ==> (pIp->value == pIp->in && *(pIp->ret) == pIp->in);
assigns pIp- > value, *(pIp- > ret);;
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