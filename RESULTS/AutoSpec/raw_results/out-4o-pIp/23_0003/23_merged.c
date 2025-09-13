typedef struct __CheckCal
{

	int		len;
	int		*pkv;
	int     chksum;
	
} CheckCal;


void main23(CheckCal *pIp)
{

	int i = 0;
	int chksum = 0;

	/*@
	loop invariant i >= 0 && i <= pIp->len;
	loop invariant i >= 0 && chksum >= 0;
	loop invariant i == pIp->len ==> pIp->chksum == chksum;
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant 0 <= chksum;
	loop invariant 0 < chksum;
	loop invariant i == 0 ==> chksum == 0;
	loop invariant 0 <= i;
	loop assigns i;
	loop assigns chksum;
	*/
	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	
	// @ assert pIp->len == \at(pIp->len,Pre);
	// @ assert (chksum == 0) || (chksum == sum(pIp->pkv, 0, pIp->len));


	pIp->chksum = chksum;


	return;
}






