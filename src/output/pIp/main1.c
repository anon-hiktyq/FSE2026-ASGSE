


typedef struct __TripleAbsMax
{
    int abs[3];
    int tmax;
    int* ret;
} TripleAbsMax;

/*@
    requires \valid(pIp);                               // Pointer pIp must be valid
    requires \valid(pIp->abs+(0..2));                   // The abs array must have 3 valid elements
    requires \valid(pIp->ret);                          // Pointer ret must be valid
    requires \separated(pIp, pIp->ret);                 // pIp and pIp->ret must not overlap
    ensures pIp->tmax == \max(\max(\abs(pIp->abs[0]), \abs(pIp->abs[1])), \abs(pIp->abs[2])); // tmax is the maximum absolute value
    ensures *(pIp->ret) == pIp->tmax;                   // The value pointed to by ret is updated to tmax
    assigns pIp->tmax, *(pIp->ret);                     // Function modifies tmax and the value pointed to by ret
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
/*@
    requires \valid(pIp);
requires \valid(pIp->abs+(0..2));
requires \valid(pIp->ret);
requires \separated(pIp, pIp->ret);
    */
    
void main1(TripleAbsMax *pIp)
{

	pIp -> abs[0] = 1;
	pIp -> abs[1] = 2;
	pIp -> abs[2] = -3;

	TripleAbsMaxFun(pIp);

    /*@ assert pIp -> tmax == 3; */
}