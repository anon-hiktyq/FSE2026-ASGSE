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
	loop invariant chksum == \sum(0, i, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] >= 0;
	loop assigns i, chksum;
	*/
	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	pIp->chksum = chksum;

	// @ assert chksum >= 0;

	return;
}






