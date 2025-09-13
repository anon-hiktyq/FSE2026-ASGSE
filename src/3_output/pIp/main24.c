
typedef struct __CheckCal
{
    int len;
    int *pkv;
    int chksum;
} CheckCal;

/*@
  logic integer sum(int* array, integer begin, integer end) = 
    \sum(k; begin <= k < end ==> array[k]);
*/

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv+(0..9));
    requires pIp->len <= 10;
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp -> pkv[i] && pIp -> pkv[i] <= 100;
*/
void main24(CheckCal *pIp)
{
    int i = 0;
    int chksum = 0;

    /*@ loop invariant 0 <= i <= pIp->len;
        loop invariant chksum == sum(pIp->pkv, 0, i);
        loop assigns chksum, i;
    */
    for(; i < pIp -> len; i++)
    {
        chksum = chksum + pIp -> pkv[i];
    }

    /*@ assert chksum >= 0; */
    
    pIp->chksum = chksum;

    return;
}
