

typedef struct __LimitInt32
{
	int			in;
	int		    bound;
	int		    value;
	int*		ret;
} LimitInt32;


/*@
```c
requires \valid(pIp);
requires \valid(pIp->ret);
requires pIp->bound >= 0;
ensures pIp->in > pIp->bound ==> pIp->value == pIp->bound;
ensures pIp->in < -pIp->bound ==> pIp->value == -pIp->bound;
ensures -pIp->bound <= pIp->in <= pIp->bound ==> pIp->value == pIp->in;
ensures *(pIp->ret) == pIp->value;
ensures -pIp->bound <= pIp->value <= pIp->bound;
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


void main31(LimitInt32 *pIp)
{
	pIp -> in = 100;
	pIp -> bound = 50;

	LimitInt32Fun(pIp);

    // @ assert pIp -> value == 50;
	// @ assert *(pIp -> ret) == 50;
}