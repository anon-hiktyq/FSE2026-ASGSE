
typedef struct __CheckCal
{
        int pkv[10];
        int len;
        int chksum;

} CheckCal;

/*@
axiomatic Sum_array {
    logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
    axiom empty:
        \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
    axiom range:
        \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1) + a[e-1];
}
*/

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] <= 100;
    requires pIp->len <= 10;
    ensures pIp->chksum == sum(&pIp->pkv[0], 0, pIp->len);
    ensures \forall integer k; 0 <= k < 10 ==> pIp->pkv[k] == \at(pIp->pkv[k],Pre);
    ensures pIp->len == \at(pIp->len,Pre);
    assigns pIp->chksum;
*/
void CheckCalFun4(CheckCal *pIp){
        int i = 0;
        int chksum = 0;

        /*@
          loop invariant (0 < \at(pIp,Pre)->len) ==> (0 <= i <= \at(pIp,Pre)->len);
          loop invariant (0 < \at(pIp,Pre)->len) ==> (chksum == sum(&pIp->pkv[0], 0, i));
          loop invariant (pIp->len == 0) ==> (chksum == 0);
          loop invariant pIp == \at(pIp,Pre);
          loop invariant \at(pIp,Pre)->len == \at(pIp->len,Pre);
          loop invariant \at(pIp,Pre)->chksum == \at(pIp->chksum,Pre);
          loop invariant \forall integer k; 0 <= k < 10 ==> pIp->pkv[k] == \at(pIp->pkv[k],Pre);
          loop assigns i, chksum;
        */
        for (; i < pIp->len; i++){
            chksum = chksum + pIp->pkv[i];
        }

        pIp->chksum = chksum;
   }
   