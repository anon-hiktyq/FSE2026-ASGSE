typedef struct __CheckCal
{

	int		len;
	int		*pkv;
	int     chksum;
	
} CheckCal;


void main24(CheckCal *pIp)
{

	int i = 0;
	int chksum = 0;

	/*@
	loop invariant 0 <= i <= pIp->len;
	loop invariant chksum == \sum(0, i-1, pIp->pkv[\old(i)]);
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant chksum >= 0;
	loop invariant 0 <= i;
	loop assigns i;
	loop assigns chksum;
	*/
	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	pIp->chksum = chksum;

	// @ assert chksum >= 0;

	return;
}






