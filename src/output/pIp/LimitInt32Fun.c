typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;

/*@
requires \valid(pIp) && \valid(pIp->ret);
requires \separated(pIp,pIp->ret);

ensures \old(pIp->in) >= -\old(pIp->bound) && \old(pIp->in) <= \old(pIp->bound) ==> pIp->in == \old(pIp->in)&&pIp->bound == \old(pIp->bound)&&pIp->value == \old(pIp->in)&&pIp->ret == \old(pIp->ret)&&*pIp->ret == \old(pIp->in);

ensures \old(pIp->in) < -\old(pIp->bound) && \old(pIp->in) <= \old(pIp->bound) ==> pIp->in == \old(pIp->in)&&pIp->bound == \old(pIp->bound)&&pIp->value == -\old(pIp->bound)&&pIp->ret == \old(pIp->ret)&&*\old(pIp->ret) == -\old(pIp->bound);

ensures \old(pIp->in) > \old(pIp->bound) ==> pIp->in == \old(pIp->in)&&pIp->bound == \old(pIp->bound)&&pIp->value == \old(pIp->bound)&&pIp->ret == \old(pIp->ret)&&*pIp->ret == \old(pIp->bound);

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