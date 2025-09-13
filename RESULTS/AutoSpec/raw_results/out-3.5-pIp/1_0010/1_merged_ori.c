
typedef struct __TripleAbsMax
{
    int abs[3];
    int tmax;
    int* ret;
} TripleAbsMax;


/*@
requires \valid(pIp- > ret);
requires \valid(pIp);
requires \separated(pIp, pIp- > ret);
ensures pIp->tmax >= 0;
ensures pIp- > tmax == \max(\abs(pIp- > abs[0]), \max(\abs(pIp- > abs[1]), \abs(pIp- > abs[2])));
ensures *(pIp- > ret) == pIp- > tmax;
assigns pIp- > tmax, *(pIp- > ret);
```c;
```;
Looking at this function, I need to specify the contract for `TripleAbsMaxFun` which computes the maximum absolute value of three integers and stores it in both `tmax` and the location pointed to by `ret`.;
*/
void TripleAbsMaxFun(TripleAbsMax *pIp)
{
    
    int absfx1 = pIp->abs[0];
    int absfy2 = pIp->abs[1];
    int absfz3 = pIp->abs[2];

    if (pIp->abs[0] < 0)
    {
        absfx1 = -pIp->abs[0];
    }

    if (pIp->abs[1] < 0)
    {
        absfy2 = -pIp->abs[1];
    }

    if (pIp->abs[2] < 0)
    {
        absfz3 = -pIp->abs[2];
    }

    if (absfx1 > absfy2)
    {
        pIp->tmax = absfx1;
    }
    else
    {
        pIp->tmax = absfy2;
    }

    if (absfz3 > pIp->tmax)
    {
        pIp->tmax = absfz3;
    }

    *(pIp->ret) = pIp->tmax;


}


void main1(TripleAbsMax *pIp)
{

	pIp -> abs[0] = 1;
	pIp -> abs[1] = 2;
	pIp -> abs[2] = -3;

	TripleAbsMaxFun(pIp);

    // @ assert pIp -> tmax == 3;
}