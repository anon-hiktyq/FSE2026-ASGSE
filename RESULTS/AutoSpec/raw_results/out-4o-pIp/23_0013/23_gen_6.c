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
	loop invariant \forall integer j; 0 <= j < i ==> chksum == \sum(0, j, pIp->pkv[j]);
	loop invariant 0 <= i <= pIp->len;
	loop invariant chksum >= 0;
	loop invariant \forall integer j; i <= j < pIp->len ==> chksum + \sum(i, j, pIp->pkv[j]) == \sum(0, pIp->len -1, pIp->pkv[j]);
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






