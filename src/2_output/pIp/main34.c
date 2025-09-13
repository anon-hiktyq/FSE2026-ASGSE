
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
Ensure (0 >= pIp_delaytime && pIp->delaytime == pIp_delaytime)
*/
{

    int t=0;

   
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv emp */ /*0*/ 
 for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    

    return ;
}
void main34(Delay *pIp)
/*@
With pIp_delaytime
Require pIp->delaytime == pIp_delaytime
Ensure emp
*/{
    pIp -> delaytime = 10;

    DelayFun(pIp);

    
}