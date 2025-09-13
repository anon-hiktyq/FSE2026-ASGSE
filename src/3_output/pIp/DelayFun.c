
typedef struct __Delay
{
    int delaytime;
} Delay;

/*@
  predicate delaytime_positive(Delay* pIp) = pIp->delaytime > 0;
*/

/*@
    requires \valid(pIp) && pIp->delaytime >= 0;
*/
void DelayFun(Delay* pIp)
{
    int t = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant !delaytime_positive(pIp) ==> (t == 0 && pIp == pIp && pIp->delaytime == pIp->delaytime);
      loop invariant pIp == pIp;
      loop invariant pIp->delaytime == pIp->delaytime;
      loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

    /*@ assert t >= 0; */

    return;
}
