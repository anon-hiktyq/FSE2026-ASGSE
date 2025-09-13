

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
ensures pIp->value >= -pIp->bound && pIp->value <= pIp->bound;
ensures *(pIp->ret) == pIp->value;
ensures (pIp->in > pIp->bound ==> pIp->value == pIp->bound) &&
        (pIp->in < -pIp->bound ==> pIp->value == -pIp->bound) &&
        (-pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in);
assigns pIp->value;
assigns *(pIp->ret);
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


void main28(LimitInt32 *pIp)
{
	pIp -> in = 100;
	pIp -> bound = 50;

	LimitInt32Fun(pIp);

    // @ assert pIp -> value == 50;
	// @ assert *(pIp -> ret) == 50;
    // @ assert pIp -> in == 100;
    // @ assert pIp -> bound == 50;
}