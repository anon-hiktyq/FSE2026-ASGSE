
typedef struct __TripleAbsMax
{
    int abs[3];
    int tmax;
    int* ret;
} TripleAbsMax;

/*@
requires \valid(pIp); 
requires \valid(pIp->abs+(0..2));
requires \valid(pIp->ret);
requires \separated(pIp, pIp->ret);

ensures pIp->abs[0] == \old(pIp->abs[0]) && pIp->abs[1] == \old(pIp->abs[1]) && pIp->abs[2] == \old(pIp->abs[2]) &&
        (-pIp->abs[2] <= pIp->abs[1] && pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[1]) &&
        (-pIp->abs[2] <= pIp->abs[1] && -pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[1]) &&
        (-pIp->abs[2] <= -pIp->abs[1] && -pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[1]) &&
        (-pIp->abs[2] <= -pIp->abs[1] && pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == -pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[1]) &&
        (pIp->abs[2] <= -pIp->abs[1] && pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == -pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[1]) &&
        (pIp->abs[2] <= -pIp->abs[1] && -pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[1]) &&
        (pIp->abs[2] <= pIp->abs[1] && -pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[1]) &&
        (pIp->abs[2] <= pIp->abs[1] && pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[1] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[1]) &&
        (-pIp->abs[2] <= pIp->abs[0] && pIp->abs[0] > pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[0]) &&
        (-pIp->abs[2] <= -pIp->abs[0] && -pIp->abs[0] > pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[0]) &&
        (-pIp->abs[2] <= -pIp->abs[0] && -pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[0]) &&
        (-pIp->abs[2] <= pIp->abs[0] && pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[0]) &&
        (pIp->abs[2] <= pIp->abs[0] && pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[0]) &&
        (pIp->abs[2] <= -pIp->abs[0] && -pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[0]) &&
        (pIp->abs[2] <= -pIp->abs[0] && -pIp->abs[0] > pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[0]) &&
        (pIp->abs[2] <= pIp->abs[0] && pIp->abs[0] > pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[0] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[0]) &&
        (pIp->abs[2] > pIp->abs[0] && pIp->abs[0] > pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (pIp->abs[2] > -pIp->abs[0] && -pIp->abs[0] > pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (pIp->abs[2] > -pIp->abs[0] && -pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (pIp->abs[2] > pIp->abs[0] && pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (-pIp->abs[2] > pIp->abs[0] && pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (-pIp->abs[2] > -pIp->abs[0] && -pIp->abs[0] > -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (-pIp->abs[2] > -pIp->abs[0] && -pIp->abs[0] > pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (-pIp->abs[2] > pIp->abs[0] && pIp->abs[0] > pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (pIp->abs[2] > pIp->abs[1] && pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (pIp->abs[2] > pIp->abs[1] && -pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (pIp->abs[2] > -pIp->abs[1] && -pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (pIp->abs[2] > -pIp->abs[1] && pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] >= 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == pIp->abs[2]) &&
        (-pIp->abs[2] > -pIp->abs[1] && pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] >= 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (-pIp->abs[2] > -pIp->abs[1] && -pIp->abs[0] <= -pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] < 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (-pIp->abs[2] > pIp->abs[1] && -pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] < 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]) &&
        (-pIp->abs[2] > pIp->abs[1] && pIp->abs[0] <= pIp->abs[1] && pIp->abs[2] < 0 && pIp->abs[1] >= 0 && pIp->abs[0] >= 0 ==> pIp->tmax == -pIp->abs[2] && pIp->ret == \old(pIp->ret) && *\old(pIp->ret) == -pIp->abs[2]);
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
    
void main3(TripleAbsMax *pIp)
{

	pIp -> abs[0] = 1;
	pIp -> abs[1] = 2;
	pIp -> abs[2] = -3;

	TripleAbsMaxFun(pIp);

    /*@ assert pIp->abs[0] == 1; */
    /*@ assert pIp->abs[1] == 2; */
    /*@ assert pIp->abs[2] == -3; */
}
