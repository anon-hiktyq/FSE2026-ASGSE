typedef struct __DevControl
{
  int * p1;
  int * p2;
  int * p3;

} DevControl;

/*@
requires \valid(pIp);

ensures pIp->p1 == \old(pIp->p1)&&*pIp->p1 == 60306&&pIp->p2 == \old(pIp->p2)&&*pIp->p2 == 1&&pIp->p3 == \old(pIp->p3)&&*pIp->p3 == 252;

*/

void DevControlFun(DevControl *pIp)

{
	*(pIp->p1)= 0xEB92;

	*(pIp->p2)= 0x01;

	*(pIp->p3)= 0xFC;

	return;
}