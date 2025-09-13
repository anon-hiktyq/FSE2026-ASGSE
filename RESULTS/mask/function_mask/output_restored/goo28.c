typedef struct __Delay
{

	int			delaytime;

} Delay;


typedef struct __Delay
{
    int delaytime;
} Delay;

/*@
axiomatic DelayProperties {
    logic integer delaytime_value(Delay* pIp) reads pIp->delaytime;
    axiom delaytime_initial:
        \forall Delay* pIp; delaytime_value(pIp) == pIp->delaytime;
}
*/

/*@
requires \valid(pIp);
requires 0 <= pIp->delaytime <= 10;
*/
void DelayFun(Delay* pIp)
{
    int t = 0;

    /*@
    loop invariant 0 <= t <= pIp->delaytime;
    loop invariant (0 < delaytime_value(pIp)) ==> (t >= 0 && t <= delaytime_value(pIp));
    loop invariant (!(0 < delaytime_value(pIp))) ==> ((t == 0) && (pIp == \at(pIp, Pre)) && (delaytime_value(pIp) == pIp->delaytime));
    loop invariant pIp == \at(pIp, Pre);
    loop invariant delaytime_value(pIp) == pIp->delaytime;
    loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

    /*@ assert t >= 0; */

    return;
}
/*@
    requires \valid(pIp);
    */
    
void goo28(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}