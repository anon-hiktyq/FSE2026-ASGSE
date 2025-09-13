

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
ensures pIp->value >= -pIp->bound;
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound;
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound && *(pIp->ret) == pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound && *(pIp->ret) == -pIp->bound;
ensures pIp- > value == \old(pIp- > in) || pIp- > value == pIp- > bound || pIp- > value == -pIp- > bound;
ensures pIp- > value == \min(pIp- > bound, \max(-pIp- > bound, pIp- > in));
ensures pIp- > value <= pIp- > bound;
ensures \result > \old(pIp->bound) ==> pIp->value == \old(pIp->bound);
ensures \result == \old(pIp->in) ==> pIp->value == \old(pIp->in);
ensures \result == 0;
ensures \result < -\old(pIp->bound) ==> pIp->value == -\old(pIp->bound);
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in && *(pIp->ret) == pIp->in;
ensures -pIp- > bound <= pIp- > value <= pIp- > bound;
ensures *(pIp- > ret) == pIp- > value;
ensures (pIp->in > pIp->bound) ==> pIp->value == pIp->bound;
ensures (pIp->in > pIp->bound ==> pIp->value == pIp->bound) &&;
ensures (pIp->in < -pIp->bound) ==> pIp->value == -pIp->bound;
ensures (-pIp->bound <= pIp->in <= pIp->bound) ==> pIp->value == pIp->in;
assigns pIp- > value;
assigns pIp- > value, *(pIp- > ret);
assigns *(pIp- > ret);
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

/*@
requires \valid(pIp);
requires \valid(pIp->ret);
*/
void main26(LimitInt32 *pIp)
{
	pIp -> in = -200;
	pIp -> bound = 100;

	LimitInt32Fun(pIp);

    // @ assert pIp->value == -100;
	// @ assert *(pIp -> ret) == -100;
}