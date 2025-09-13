

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
requires \valid(pIp) && \valid(pIp- > ret);
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound;
ensures \result == pIp->in ==> pIp->value == pIp->in;
ensures \result == \old(pIp->in) ==> \result == pIp->in;
ensures \result == \null;
ensures \result == *(pIp- > ret);
ensures \result != \old(pIp->in) ==> \result == pIp->value;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in;
ensures -pIp- > bound <= \result <= pIp- > bound;
ensures *(pIp- > ret) == pIp- > value;
ensures (pIp->in > pIp->bound) ==> pIp->value == pIp->bound;
ensures (pIp->in > pIp->bound ==> pIp->value == pIp->bound);
ensures (pIp->in > pIp->bound ==> pIp->value == pIp->bound) &&;
ensures (pIp->in < -pIp->bound) ==> pIp->value == -pIp->bound;
ensures (pIp->in < -pIp->bound ==> pIp->value == -pIp->bound);
ensures (\result == \null ==> (pIp->in > pIp->bound ==> pIp->value == pIp->bound && *(pIp->ret) == pIp->bound));
ensures (\result == \null ==> (pIp->in < -pIp->bound ==> pIp->value == -pIp->bound && *(pIp->ret) == -pIp->bound));
ensures (\result == \null ==> (-pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in && *(pIp->ret) == pIp->in));
ensures (-pIp->bound <= pIp->in <= pIp->bound) ==> pIp->value == pIp->in;
ensures (-pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in);
assigns pIp- > value, *(pIp- > ret);
(pIp->in < -pIp->bound ==> pIp->value == -pIp->bound) &&;
(-pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in);
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


void main27(LimitInt32 *pIp)
{
	pIp -> in = 0;
	pIp -> bound = 0;

	LimitInt32Fun(pIp);

    // @ assert pIp->value == 0;
	// @ assert *(pIp -> ret) == 0;
}