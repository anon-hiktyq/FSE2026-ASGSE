

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
ensures pIp->value == \min(pIp->bound, \max(-pIp->bound, pIp->in));
ensures *(pIp->ret) == pIp->value;
ensures pIp->in == \old(pIp->in);
ensures pIp->bound == \old(pIp->bound);
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