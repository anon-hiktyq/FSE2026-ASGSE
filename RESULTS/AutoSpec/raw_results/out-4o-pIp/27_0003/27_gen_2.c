

typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;



/*@
```c
requires \valid(pIp) && \valid(pIp->ret);
requires pIp->bound >= 0;
ensures pIp->value == ((pIp->in > pIp->bound) ? pIp->bound : ((pIp->in < -pIp->bound) ? -pIp->bound : pIp->in));
ensures *(pIp->ret) == pIp->value;
assigns pIp->value, *(pIp->ret);
```
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