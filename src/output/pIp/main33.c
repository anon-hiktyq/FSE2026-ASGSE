
typedef struct __Delay
{
    int delaytime;
} Delay;

/*@
requires \valid(pIp);
ensures \forall int old_delaytime; \old(pIp->delaytime) == old_delaytime ==> pIp->delaytime == old_delaytime;
*/

void DelayFun(Delay* pIp)
{
    int t = 0;

    /*@
      loop invariant 0 <= t <= \max(0, pIp->delaytime);
      loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

    /*@ assert t >= 0; */

    return;
}

/*@ requires \valid(pIp);
*/

void main33(Delay *pIp)
{
    pIp->delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp->delaytime == 10; */
}
