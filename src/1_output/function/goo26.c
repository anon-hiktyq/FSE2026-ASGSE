
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
    ((0 < pIp@pre->delaytime) => (t >= 0 && t <= pIp@pre->delaytime)) &&
((!(0 < pIp@pre->delaytime)) => ((t == 0) && (pIp == pIp@pre) && (pIp@pre->delaytime == pIp_delaytime))) &&
(pIp == pIp@pre) &&
(pIp@pre->delaytime == pIp_delaytime) &&
(delay_count(pIp, t) == t
    loop assigns t)
    */
    
    for (; t < pIp->delaytime; t++)
    {
        ;
    }
    
    

    return ;
}
void goo26(Delay *pIp)
/*@
With pIp_delaytime
Require pIp->delaytime == pIp_delaytime
Ensure emp
*/{

    pIp -> delaytime = 10;

    DelayFun(pIp);

    
}