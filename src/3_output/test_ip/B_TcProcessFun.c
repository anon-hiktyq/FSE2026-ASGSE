

typedef struct __B_TcProcess
{

	int			tcaData[3];
	int         chksum;
	int 		len;
	int     	flgMode;

} B_TcProcess;

void CheckCal(B_TcProcess *pIp)
{

	int i = 0;
	int chksum = 0;

	for(; i< pIp -> len; i++)
	{
	    chksum = chksum + pIp->tcaData[i];
	}

	pIp->chksum = chksum;

	return;
}

void B_TcProcessFun(B_TcProcess *pIp)
{

	int chksum;
	unint08 i;

	if ((pIp -> tcaData[0] == 0xE1) && (pIp -> tcaData[1] == 0x00))
	{

		CheckCal(pIp);

	    if(pIp -> tcaData[3] == chksum)
	    {

	    	if(pIp -> tcaData[2] == 0)
	    	{
	    		pIp->flgMode = 0x00 ;
	    	}
	    	else if(pIp -> tcaData[2] == 1)
	    	{
	    		pIp->flgMode = 0x33 ;
	    	}
	    	else
	    	{
	    		pIp->flgMode = 0x44 ;
	    	}
	    }
	}

	return;
}