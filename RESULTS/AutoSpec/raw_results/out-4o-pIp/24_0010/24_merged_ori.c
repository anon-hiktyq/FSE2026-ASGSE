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
	loop invariant pIp- > chksum == 0;
	loop invariant len < pIp-;
	loop invariant i >= 0 && chksum >= 0;
	loop invariant i == 0 || chksum >= pIp->pkv[i-1];
	loop invariant i <= pIp-;
	loop invariant chksum == \sum(0, i-1, λ k; pIp- > pkv[k]);
	loop invariant chksum == \sum(0, i-1, pIp- > pkv[k]);
	loop invariant chksum == \sum(0, i-1, pIp- > pkv[\lambda]);
	loop invariant chksum == \sum(0, i-1, pIp- > pkv);
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, λ m; pIp->pkv[m]);
	loop invariant \forall integer j; 0 <= j < i ==> chksum >= pIp->pkv[j];
	loop invariant \exists integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv[\lambda]);
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






