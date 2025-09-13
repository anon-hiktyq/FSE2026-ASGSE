

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
assigns pIp->value;
assigns *(pIp->ret);
ensures \result == \old(pIp->in) ==> pIp->value == \old(pIp->in);
ensures \result > \old(pIp->bound) ==> pIp->value == \old(pIp->bound);
ensures \result < -\old(pIp->bound) ==> pIp->value == -\old(pIp->bound);
ensures *(pIp->ret) == pIp->value;
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