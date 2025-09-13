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
	loop invariant i <= pIp->len;
	loop invariant chksum == \sum(pIp->pkv, 0, i);
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= \sum(pIp->pkv, 0, k);
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
    // @ assert chksum >= 0;

	pIp->chksum = chksum;


	return;
}