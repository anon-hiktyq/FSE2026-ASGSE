
typedef struct __DevControl
{
  int * p1;
  int * p2;
  int * p3;

} DevControl;

/*@
requires \valid(pIp) && \valid(pIp->p1) && \valid(pIp->p2) && \valid(pIp->p3);
assigns *pIp->p1, *pIp->p2, *pIp->p3;
ensures *pIp->p1 == 60306 &&
        *pIp->p2 == 1 &&
        *pIp->p3 == 252;
*/
void DevControlFun(DevControl *pIp)
{
	*(pIp->p1) = 0xEB92; // 60306 in decimal
	*(pIp->p2) = 0x01;   // 1 in decimal
	*(pIp->p3) = 0xFC;   // 252 in decimal
	return;
}

/*@
requires \valid(pIp);
assigns pIp->p1, pIp->p2, pIp->p3;
ensures pIp->p1 == \old(pIp->p1) &&
        pIp->p2 == \old(pIp->p2) &&
        pIp->p3 == \old(pIp->p3);
*/
void goo18(DevControl *pIp)
{
	pIp->p1 = 0x0000;
	pIp->p2 = 0x0000;
	pIp->p3 = 0x0000;

	DevControlFun(pIp);
	
	/*@ assert *(pIp->p1) == 0xEB92; */
	/*@ assert *(pIp->p2) == 0x01; */
	/*@ assert *(pIp->p3) == 0xFC; */	

}
