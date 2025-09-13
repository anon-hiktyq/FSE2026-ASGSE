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
	loop invariant len < pIp-;
	loop invariant i <= pIp-;
	loop invariant chksum == \sum(0, i, pIp- > pkv);
	loop invariant chksum == \sum(0, i, (\lambda integer k; pIp- > pkv[k]));
	loop invariant chksum == \sum(0, i - 1, \lambda integer k; pIp- > pkv[k]);
	loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] == \at(pIp->pkv[k], Pre);
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, pIp->pkv);
	loop invariant \forall integer k; 0 <= k < i ==> chksum == \sum(0, k, \lambda integer l; pIp->pkv[l]);
	loop invariant \forall integer k; 0 <= k < i ==> \valid(&(pIp->pkv[k]));
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






