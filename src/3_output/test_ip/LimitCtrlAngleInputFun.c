
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
{

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


void LimitCtrlAngleInputFun(LimitCtrlAngleInput *pIp)
{

    pIp -> pSCtrl0->Up = pIp -> pSA->angle[0] ;
    pIp -> pSCtrl1->Up = pIp -> pSA->angle[1] ;
    pIp -> pSCtrl2->Up = 0 ;

	LimitAngle(pIp);

	return;
}