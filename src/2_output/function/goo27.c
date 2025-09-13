
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __Delay
{

	int			delaytime;

} Delay;


void DelayFun(Delay* pIp)
/*@
With pIp_delaytime
Require pIp->delaytime == pIp_delaytime
Ensure emp
*/
{

    int t=0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < pIp@pre->delaytime) => (delay_progress(t, pIp->delaytime))) &&
((!(0 < pIp@pre->delaytime)) => ((t == 0) && (pIp == pIp@pre) && (pIp@pre->delaytime == pIp->delaytime@pre))) &&
(pIp == pIp@pre) &&
(pIp@pre->delaytime == pIp->delaytime@pre) &&
(0 <= t && t <= pIp->delaytime
    loop assigns t)
    */
    
    for (; t < pIp->delaytime; t++)
    {
        ;
    }
    
    

    return ;
}
void goo27(Delay *pIp)
/*@
With pIp_delaytime
Require pIp->delaytime == pIp_delaytime
Ensure emp
*/{

    pIp -> delaytime = 10;

    DelayFun(pIp);

    
}