
typedef struct __Delay
{
    int delaytime;
} Delay;

/*@
  predicate delaytime_positive(Delay* pIp) = pIp->delaytime > 0;
*/

/*@
    requires \valid(pIp) && pIp->delaytime >= 0;
    assigns \nothing; // Indicates that no observable state is modified.
    ensures pIp->delaytime == \old(pIp->delaytime); // Ensure delaytime remains unchanged.
*/
void DelayFun(Delay* pIp)
{
    int t = 0;

    /*@
      loop invariant 0 <= t <= pIp->delaytime;
      loop invariant !delaytime_positive(pIp) ==> (t == 0);
      loop invariant pIp->delaytime >= 0;
      loop assigns t; // This line is acceptable since 't' is modified in the loop.
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
    ensures pIp->delaytime == 10; // Ensure delaytime is 10 after the function call.
*/
void main32(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}
