
typedef struct __CheckCal
{
        int pkv[10];
        int len;
        int chksum;

} CheckCal;

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] <= 100;
    requires pIp->len <= 10;
    ensures pIp->chksum == \sum(0, pIp->len, pIp->pkv);
    assigns pIp->chksum;
*/
void CheckCalFun2(CheckCal *pIp){
        int i = 0;
        int chksum = 0;

        /*@
          loop invariant 0 <= i <= pIp->len;
          loop invariant chksum == \sum(0, i, pIp->pkv);
          loop invariant \forall integer j; 0 <= j < i ==> 0 <= pIp->pkv[j] <= 100;
          loop assigns i, chksum;
          loop variant pIp->len - i;
        */
        for (; i < pIp->len; i++){
            chksum = chksum + pIp->pkv[i];
        }
            
        pIp->chksum = chksum;
}
