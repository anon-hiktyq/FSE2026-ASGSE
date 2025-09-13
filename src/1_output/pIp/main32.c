
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
    (!delaytime_positive(pIp) => (t == 0 && pIp == pIp && pIp->delaytime == pIp->delaytime)) &&
(pIp == pIp) &&
(pIp->delaytime == pIp->delaytime
      loop assigns t)
    */
    
    for (; t < pIp->delaytime; t++)
    {
        ;
    }
    
    

    return ;
}
void main32(Delay *pIp)
/*@
With pIp_delaytime
Require pIp->delaytime == pIp_delaytime
Ensure emp
*/{

    pIp -> delaytime = 10;

    DelayFun(pIp);

    
}