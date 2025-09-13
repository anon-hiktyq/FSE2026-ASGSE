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
	*/
	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp -> pkv[i];
	}

	pIp->chksum = chksum;

	// @ assert chksum >= 0;

	return;
}






