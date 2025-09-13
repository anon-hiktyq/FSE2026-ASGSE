
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

    for (; t<pIp -> delaytime ; t++ )
    {
       ;
    }
    
    

    return ;
}