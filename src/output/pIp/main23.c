
/*@ 
  requires \valid(pIp);
  requires \valid(pIp->pkv + (0..9));
  requires pIp->len <= 10;
  requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp -> pkv[i] && pIp -> pkv[i] <= 100;
  ensures pIp->len == 0 ==> pIp->chksum == 0;
  ensures 0 < pIp->len ==> pIp->chksum == sum(pIp->pkv, 0, pIp->len);
*/
void main23(CheckCal *pIp)
{

	int i = 0;
	int chksum = 0;

	
            
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant 0 <= i <= pIp->len;
      loop invariant chksum == sum(pIp->pkv, 0, i);
      loop invariant \forall integer j; i <= j < pIp->len ==> pIp->pkv[j] == \at(pIp->pkv[j], Pre);
      loop invariant valid_pkvs(pIp);
      loop assigns chksum, i;
    */
    for(; i < pIp->len; i++)
	{
	    chksum = chksum + pIp->pkv[i];
	}
            

	
	/*@ assert pIp->len == \at(pIp->len, Pre); */
	/*@ assert pIp->chksum == \at(pIp->chksum, Pre); */


	pIp->chksum = chksum;


	return;
}
