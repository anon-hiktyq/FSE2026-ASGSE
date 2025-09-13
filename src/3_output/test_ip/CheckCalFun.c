
typedef struct __CheckCal
{
	int		len;
	int*	pkv;
	int     chksum;
	
} CheckCal;

/*@ 
  logic integer sum(int* arr, integer n) = 
    (n <= 0) ? 0 : arr[n-1] + sum(arr, n-1);
*/

/*@
  requires pIp != \null;
  requires pIp->pkv != \null;
  requires pIp->len >= 0;
  requires \valid(pIp->pkv + (0 .. pIp->len-1));
  ensures pIp->chksum == sum(pIp->pkv, pIp->len);
*/
void CheckCalFun(CheckCal *pIp)
{
	int i = 0;
	int chksum = 0;
	
    /*@
      loop invariant 0 <= i <= pIp->len;
      loop invariant pIp == \at(pIp,Pre);
      loop invariant \at(pIp,Pre)->len == \at(pIp->len,Pre);
      loop invariant \at(pIp,Pre)->pkv == \at(pIp->pkv,Pre);
      loop invariant *\at(pIp->pkv,Pre) == \at(*pIp->pkv,Pre);
      loop invariant \at(pIp,Pre)->chksum == \at(pIp->chksum,Pre);
    */
    for(; i < pIp->len; i++)
    {
        chksum = chksum + pIp->pkv[i];
    }
            
    pIp->chksum = chksum;

    return;
}
