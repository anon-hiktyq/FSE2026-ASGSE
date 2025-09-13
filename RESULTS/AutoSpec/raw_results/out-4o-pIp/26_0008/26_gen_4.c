

typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;



/*@
requires \valid(pIp) && \valid(pIp->ret);
ensures *(pIp->ret) == pIp->value;
ensures (pIp->in > pIp->bound ==> pIp->value == pIp->bound) &&
        (pIp->in < -pIp->bound ==> pIp->value == -pIp->bound) &&
        (-pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in);
assigns pIp->value, *(pIp->ret);
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