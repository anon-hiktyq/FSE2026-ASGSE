
typedef struct __Delay
{
    int delaytime;
} Delay;

/*@
axiomatic DelayProperties {
    logic integer delay_count(Delay* pIp, integer t);
    axiom initial_delay_count:
        \forall Delay* pIp, integer t; t == 0 ==> delay_count(pIp, t) == 0;
    axiom increment_delay_count:
        \forall Delay* pIp, integer t; t >= 0 ==> delay_count(pIp, t+1) == delay_count(pIp, t) + 1;
}
*/

/*@
requires \valid(pIp) && pIp->delaytime >= 0;
ensures delay_count(pIp, pIp->delaytime) == pIp->delaytime;
*/
void DelayFun(Delay* pIp)
{
    int t = 0;

    /*@
    loop invariant (0 < \at(pIp,Pre)->delaytime) ==> (t >= 0 && t <= \at(pIp,Pre)->delaytime);
    loop invariant (!(0 < \at(pIp,Pre)->delaytime)) ==> ((t == 0) && (pIp == \at(pIp,Pre)) && (\at(pIp,Pre)->delaytime == \at(pIp->delaytime,Pre)));
    loop invariant pIp == \at(pIp,Pre);
    loop invariant \at(pIp,Pre)->delaytime == \at(pIp->delaytime,Pre);
    loop invariant delay_count(pIp, t) == t;
    loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

    /*@
    assert delay_count(pIp, pIp->delaytime) == pIp->delaytime;
    */

    return;
}

/*@
requires \valid(pIp);
*/
void goo26(Delay *pIp)
{
    pIp->delaytime = 10;

    DelayFun(pIp);

    /* MASK_ACSL_ASSERT */
}
