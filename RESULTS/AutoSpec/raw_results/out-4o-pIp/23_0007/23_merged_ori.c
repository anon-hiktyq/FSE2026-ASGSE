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
	loop invariant \forall integer k; i <= k < pIp->len ==> pIp->pkv[k] is untouched.;
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] is accessed;
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] >= 0;
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] == \at(pIp->pkv[k], Pre);
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv) + pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv) + \sum(k, i, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k+1, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> chksum == (\sum(0, k, pIp->pkv) + pIp->pkv[k]);
	loop invariant 0 <= chksum;
	loop invariant 0 <= i;
	loop assigns pIp->pkv[0..pIp->len-1];
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






