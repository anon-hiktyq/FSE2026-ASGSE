
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (Result: Assertion) */
/*@ Extern Coq (Results: Z -> Assertion) */

    typedef struct TAG_CONTROLLERIN
{
    
    int 	Up;						
    int 	Ud;					
    int 	fy;					
    
}SController;
typedef struct TAG_ATTITUDE_PARA     	
{                                    	
	                                 	
	int 	angle[3];			 
	int 	rate[3]; 			 
	                                 	
}SAttitude;
typedef struct __LimitCtrlAngleInput
{
/* 输入端口 */
	const SAttitude*		pSA;
	const int			    max;
	/* 输出端口 */
	/* 输入输出端口 */
    SController*			pSCtrl0;
    SController*			pSCtrl1;
    SController*			pSCtrl2;
	/* 状态变量 */
	/* 参数变量 */
} LimitCtrlAngleInput;

void LimitAngle(LimitCtrlAngleInput *pIp)

/*@
With pIp_pSA_angle_l pIp_pSA_angle_0 pIp_pSA_angle_1 pIp_pSA_angle_2 pIp_pSA_rate_l pIp_pSA_rate_0 pIp_pSA_rate_1 pIp_pSA_rate_2 pIp_max pIp_pSCtrl0_Up pIp_pSCtrl0_Ud pIp_pSCtrl0_fy pIp_pSCtrl1_Up pIp_pSCtrl1_Ud pIp_pSCtrl1_fy pIp_pSCtrl2_Up pIp_pSCtrl2_Ud pIp_pSCtrl2_fy
Require store_int_array(pIp->pSA->angle,3, pIp_pSA_angle_l) && pIp_pSA_angle_l[0] == pIp_pSA_angle_0 && pIp_pSA_angle_l[1] == pIp_pSA_angle_1 && pIp_pSA_angle_l[2] == pIp_pSA_angle_2 && store_int_array(pIp->pSA->rate,3, pIp_pSA_rate_l) && pIp_pSA_rate_l[0] == pIp_pSA_rate_0 && pIp_pSA_rate_l[1] == pIp_pSA_rate_1 && pIp_pSA_rate_l[2] == pIp_pSA_rate_2 && pIp->max == pIp_max && pIp->pSCtrl0->Up == pIp_pSCtrl0_Up && pIp->pSCtrl0->Ud == pIp_pSCtrl0_Ud && pIp->pSCtrl0->fy == pIp_pSCtrl0_fy && pIp->pSCtrl1->Up == pIp_pSCtrl1_Up && pIp->pSCtrl1->Ud == pIp_pSCtrl1_Ud && pIp->pSCtrl1->fy == pIp_pSCtrl1_fy && pIp->pSCtrl2->Up == pIp_pSCtrl2_Up && pIp->pSCtrl2->Ud == pIp_pSCtrl2_Ud && pIp->pSCtrl2->fy == pIp_pSCtrl2_fy
Ensure emp
*/{

    int value;

    if (pIp -> pSCtrl0->Up > pIp -> max)
    {
        value = pIp -> max ;
    }
    else if (pIp -> pSCtrl0->Up  < -pIp -> max)
    {
        value = -pIp -> max ;
    }
    else
    {
        value = pIp -> pSCtrl0->Up ;
    }

    pIp -> pSCtrl0 ->Up = value ;

    if (pIp -> pSCtrl1->Up > pIp -> max)
    {
        value = pIp -> max ;
    }
    else if (pIp -> pSCtrl1->Up  < -pIp -> max)
    {
        value = -pIp -> max ;
    }
    else
    {
        value = pIp -> pSCtrl1->Up ;
    }

    pIp -> pSCtrl1 ->Up = value ;


}