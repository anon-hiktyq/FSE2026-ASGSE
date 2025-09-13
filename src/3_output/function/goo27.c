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
  logic integer delay_progress(integer t, integer delaytime);
  axiom delay_progress_initial:
    \forall integer t, integer delaytime; t == 0 ==> delay_progress(t, delaytime);
  axiom delay_progress_increment:
    \forall integer t, integer delaytime; delay_progress(t, delaytime) && t < delaytime ==> delay_progress(t+1, delaytime);
}
*/

/*@
requires \valid(pIp);
*/
/*@
requires pIp == \at(pIp, Pre);
*/
/*@
requires \at(pIp->delaytime, Pre) == pIp->delaytime;
*/
/*@
ensures (\at(pIp->delaytime, Pre) <= 0) ==> (\at(pIp->delaytime, Pre) == \at(pIp->delaytime, Post));
*/
/*@
ensures (\at(pIp->delaytime, Pre) > 0) ==> (\forall integer t; 0 <= t < \at(pIp->delaytime, Pre) ==> delay_progress(t, \at(pIp->delaytime, Pre)));
*/
/*@
ensures pIp == \at(pIp, Pre);
*/
void DelayFun(Delay* pIp)
{
    int t = 0;

    /*@
    loop invariant (0 < \at(pIp, Pre)->delaytime) ==> (delay_progress(t, pIp->delaytime));
    */
    /*@
    loop invariant (!(0 < \at(pIp, Pre)->delaytime)) ==> ((t == 0) && (pIp == \at(pIp, Pre)) && (\at(pIp, Pre)->delaytime == \at(pIp->delaytime, Pre)));
    */
    /*@
    loop invariant pIp == \at(pIp, Pre);
    */
    /*@
    loop invariant \at(pIp, Pre)->delaytime == \at(pIp->delaytime, Pre);
    */
    /*@
    loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

    /*@
    assert (\at(pIp->delaytime, Pre) <= 0) ==> (t == 0);
    */
    /*@
    assert (\at(pIp->delaytime, Pre) > 0) ==> (t == \at(pIp->delaytime, Pre));
    */
    return;
}
/*@
    requires \valid(pIp);
    */
    
void goo27(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    /* MASK_ACSL_ASSERT */
}