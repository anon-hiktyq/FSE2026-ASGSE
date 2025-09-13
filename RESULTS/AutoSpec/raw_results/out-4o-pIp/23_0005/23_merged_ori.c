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
	loop invariant pIp- > len == \at(pIp- > len, Pre);
	loop invariant len < pIp-;
	loop invariant i <= pIp-;
	loop invariant chksum == \sum(0, i-1, pIp- > pkv);
	loop invariant chksum == \sum(0, i, pIp- > pkv);
	loop invariant chksum == \sum(0, i - 1, pIp- > pkv[k]);
	loop invariant \forall integer k; i <= k < pIp->len ==> \sum(0, i, pIp->pkv) + \sum(i, pIp->len, pIp->pkv) == \sum(0, pIp->len, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < pIp->len ==> (\exists integer l; 0 <= l < i && pIp->pkv[l] == pIp->pkv[k]);
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv) + pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv) + \sum(k, i, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k+1, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> \exists integer x; x == pIp->pkv[k];
	loop invariant (chksum == 0) || (chksum > 0);
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






