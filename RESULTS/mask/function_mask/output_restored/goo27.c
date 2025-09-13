
typedef struct __Delay
{
    int delaytime;
} Delay;

/*@
axiomatic DelayProperties {
  logic integer delay_progress(integer t, integer delaytime);
  axiom delay_progress_initial:
    \forall integer t, integer delaytime; t == 0 ==> delay_progress(t, delaytime);
  axiom delay_progress_increment:
    \forall integer t, integer delaytime; delay_progress(t, delaytime) && t < delaytime ==> delay_progress(t+1, delaytime);
}
*/

/*@
requires \valid(pIp);
ensures (\at(pIp->delaytime, Pre) <= 0) ==> (pIp->delaytime == \at(pIp->delaytime, Pre));
ensures (\at(pIp->delaytime, Pre) > 0) ==> (\forall integer t; 0 <= t < \at(pIp->delaytime, Pre) ==> delay_progress(t, \at(pIp->delaytime, Pre)));
ensures pIp == \at(pIp, Pre);
*/
void DelayFun(Delay* pIp)
{
    int t = 0;

    /*@
    loop invariant (0 < \at(pIp->delaytime, Pre)) ==> delay_progress(t, pIp->delaytime);
    loop invariant (!(0 < \at(pIp->delaytime, Pre))) ==> (t == 0 && pIp == \at(pIp, Pre) && pIp->delaytime == \at(pIp->delaytime, Pre));
    loop invariant pIp == \at(pIp, Pre);
    loop invariant pIp->delaytime == \at(pIp->delaytime, Pre);
    loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

     /*@ assert pIp->delaytime >= 0 ==> t == pIp -> delaytime; */

    return;
}

/*@
requires \valid(pIp);
*/
void goo27(Delay *pIp)
{
    pIp->delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}
