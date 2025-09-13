

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
ensures pIp- > value == \old(pIp- > in) ?;
ensures -\old(pIp- > bound) <= pIp- > value <= \old(pIp- > bound);
ensures *(pIp- > ret) == pIp- > value;
assigns pIp- > value, *(pIp- > ret);
\old(pIp- > bound) : -\old(pIp- > bound));
(\old(pIp->in) >= -\old(pIp->bound))) :;
(\old(pIp->in) > \old(pIp->bound) ?;
((\old(pIp- > in) <= \old(pIp- > bound)) &&;
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