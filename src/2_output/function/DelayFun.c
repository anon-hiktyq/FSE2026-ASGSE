
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
*/{

    int t=0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= t && t <= pIp->delaytime) &&
((0 < delaytime_value(pIp)) => (t >= 0 && t <= delaytime_value(pIp))) &&
((!(0 < delaytime_value(pIp))) => ((t == 0) && (pIp == pIp@pre) && (delaytime_value(pIp) == pIp->delaytime))) &&
(pIp == pIp@pre) &&
(delaytime_value(pIp) == pIp->delaytime
    loop assigns t)
    */
    
    for (; t < pIp->delaytime; t++)
    {
        ;
    }
    
    

    return ;
}