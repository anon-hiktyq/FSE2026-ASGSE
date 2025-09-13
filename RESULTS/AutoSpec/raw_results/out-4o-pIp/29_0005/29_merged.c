

typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;


/*@
requires pIp->bound >= 0;
requires pIp->bound > 0;
requires \valid(pIp);
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound;
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound && *(pIp->ret) == pIp->bound;
ensures pIp->in > pIp->bound ==> *(pIp->ret) == pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound && *(pIp->ret) == -pIp->bound;
ensures pIp->in < -pIp->bound ==> *(pIp->ret) == -pIp->bound;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in && *(pIp->ret) == pIp->in;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> *(pIp->ret) == pIp->in;
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


void main29(LimitInt32 *pIp)
{
	pIp -> in = -200;
	pIp -> bound = 100;

	LimitInt32Fun(pIp);

    // @ assert pIp->value == -100;
	// @ assert *(pIp -> ret) == -100;
    // @ assert pIp -> in == -200;
    // @ assert pIp -> bound == 100;
}