

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
ensures pIp->value == \old(pIp->in) ? 
         ((\old(pIp->in) <= \old(pIp->bound)) && 
          (\old(pIp->in) >= -\old(pIp->bound))) : 
         (\old(pIp->in) > \old(pIp->bound) ? 
           \old(pIp->bound) : -\old(pIp->bound));
ensures *(pIp->ret) == pIp->value;
ensures -\old(pIp->bound) <= pIp->value <= \old(pIp->bound);
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