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
	loop invariant len < pIp-;
	loop invariant i <= pIp-;
	loop invariant i <= pIp -> len;
	loop invariant chksum == \sum(0, i-1, pIp->pkv[\forall integer k; 0 <= k < i ==> pIp->pkv[k]]);
	loop invariant chksum == \sum(0, i-1, pIp- > pkv[k]);
	loop invariant chksum == \sum(0, i-1, pIp- > pkv);
	loop invariant chksum == \sum(0, i, pIp- > pkv);
	loop invariant chksum == \sum(0, i - 1, pIp- > pkv[\lambda]);
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> (chksum == \sum(0, k-1, pIp->pkv[m]) + pIp->pkv[k]);
	loop invariant \exists integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv) + \sum(k+1, i, pIp->pkv);
	loop invariant 0 <= pIp->len;
	loop invariant 0 <= chksum;
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






