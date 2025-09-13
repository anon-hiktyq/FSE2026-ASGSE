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
	loop invariant \forall integer j; 0 <= j < i ==> \exists integer k; 0 <= k < i && pIp->pkv[k] == pIp->pkv[j];
	loop invariant 0 <= i;
	loop assigns pIp->pkv[0..pIp->len-1];
	loop assigns i;
	loop assigns chksum;
	*/
	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	
	//@ assert pIp->len == \at(pIp->len,Pre);
	//@ assert (chksum == 0) || (chksum == sum(pIp->pkv, 0, pIp->len));


	pIp->chksum = chksum;


	return;
}






