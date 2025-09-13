
#include <stdint.h>

typedef struct __B_TcProcess
{
    int tcaData[3];
    int chksum;
    int len;
    int flgMode;
} B_TcProcess;

void CheckCal(B_TcProcess *pIp)
{
    int i = 0;
    int chksum = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant 0 <= i <= pIp->len;
      loop invariant chksum == (\forall integer j; 0 <= j < i ==> chksum == \sum(0, j, pIp->tcaData[j]));
      loop invariant pIp == \at(pIp,Pre);
      loop invariant \at(pIp,Pre)->chksum == \at(pIp->chksum,Pre);
      loop invariant \at(pIp,Pre)->len == pIp->len;
      loop invariant \at(pIp,Pre)->flgMode == \at(pIp->flgMode,Pre);
    */
    for(; i < pIp->len; i++)
    {
        chksum = chksum + pIp->tcaData[i];
    }

    pIp->chksum = chksum;

    return;
}

void B_TcProcessFun(B_TcProcess *pIp)
{
    int chksum;
    uint8_t i;

    if ((pIp -> tcaData[0] == 0xE1) && (pIp -> tcaData[1] == 0x00))
    {
        CheckCal(pIp);

        if(pIp -> tcaData[3] == chksum)
        {
            if(pIp -> tcaData[2] == 0)
            {
                pIp->flgMode = 0x00;
            }
            else if(pIp -> tcaData[2] == 1)
            {
                pIp->flgMode = 0x33;
            }
            else
            {
                pIp->flgMode = 0x44;
            }
        }
    }

    return;
}
