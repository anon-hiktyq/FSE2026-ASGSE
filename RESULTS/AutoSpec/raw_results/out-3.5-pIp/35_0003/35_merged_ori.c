

typedef struct __DevControl
{
  int * p1;
  int * p2;
  int * p3;

} DevControl;


/*@
requires \valid(pIp- > p3);
requires \valid(pIp- > p2);
requires \valid(pIp- > p1);
requires \valid(pIp);
ensures *(pIp- > p3) == 0xFC;
ensures *(pIp- > p2) == 0x01;
ensures *(pIp- > p1) == 0xEB92;
assigns *(pIp- > p1), *(pIp- > p2), *(pIp- > p3);
```c;
```;
*/
void DevControlFun(DevControl *pIp)
{
	*(pIp->p1)= 0xEB92;

	*(pIp->p2)= 0x01;

	*(pIp->p3)= 0xFC;

	return;
}

void main35(DevControl *pIp)
{

	pIp -> p1 = 0x0000;
	pIp -> p2 = 0x0000;
	pIp -> p3 = 0x0000;

	DevControlFun(pIp);

	// @ assert *(pIp->p1) == 0xEB92;
	// @ assert *(pIp->p2) == 0x01;
	// @ assert *(pIp->p3) == 0xFC;	

}