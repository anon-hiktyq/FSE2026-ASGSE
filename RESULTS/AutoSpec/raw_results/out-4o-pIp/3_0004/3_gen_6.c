
typedef struct __TripleAbsMax
{
    int abs[3];
    int tmax;
    int* ret;
} TripleAbsMax;


/*@
requires \valid(pIp) && \valid(pIp->ret);
assigns pIp->tmax, *(pIp->ret);
ensures 0 <= \result <= 2;
ensures *(pIp->ret) == pIp->tmax;
ensures pIp->tmax == \max(\abs(pIp->abs[0]), \abs(pIp->abs[1]), \abs(pIp->abs[2]));
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


void main3(TripleAbsMax *pIp)
{

	pIp -> abs[0] = 1;
	pIp -> abs[1] = 2;
	pIp -> abs[2] = -3;

	TripleAbsMaxFun(pIp);

    // @ assert pIp->abs[0] == \at(pIp->abs[0], Pre);
    // @ assert pIp->abs[1] == \at(pIp->abs[1], Pre);
    // @ assert pIp->abs[2] == \at(pIp->abs[2], Pre);
}