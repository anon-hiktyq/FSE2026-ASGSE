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
	loop invariant i <= pIp -> len;
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= pIp->pkv[k];
	loop invariant \forall integer k; 0 <= k < i ==> chksum >= 0;
	loop invariant \forall integer j; 0 <= j < i ==> chksum >= pIp->pkv[j];
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






