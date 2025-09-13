typedef struct __CheckCal
{

	int		len;
	int		*pkv;
	int     chksum;
	
} CheckCal;


void main25(CheckCal *pIp)
{

	int i = 0;
	int chksum = 0;

	/*@
	loop invariant 0 <= i <= pIp->len;
	loop invariant chksum == \sum(0, i-1, pIp->pkv[k]);
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= 0;
	loop assigns i, chksum;
	*/
	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	
	// @ assert pIp->len == \at(pIp->len,Pre);
	// @ assert (chksum == 0) || (chksum == sum(pIp->pkv, 0, pIp->len));
    // @ assert chksum >= 0;

	pIp->chksum = chksum;


	return;
}