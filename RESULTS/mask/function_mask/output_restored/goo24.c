
typedef struct __CheckCal
{
    int len;
    int *pkv;
    int chksum;
} CheckCal;

/*@
axiomatic SumArray {
    logic integer sum(int* array, integer begin, integer end) reads array[begin .. end-1];
    axiom empty: \forall int* a, integer b, e; b >= e ==> sum(a, b, e) == 0;
    axiom range: \forall int* a, integer b, e; b < e ==> sum(a, b, e) == sum(a, b, e-1) + a[e-1];
}
*/

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires pIp->len <= 10;
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] && pIp->pkv[i] <= 100;
    ensures pIp->chksum == sum(pIp->pkv, 0, pIp->len);
*/
void goo24(CheckCal *pIp)
{
    int i = 0;
    int chksum = 0;

    /*@
      loop invariant pIp == \at(pIp, Pre);
      loop invariant \at(pIp, Pre)->len == pIp->len;
      loop invariant \at(pIp, Pre)->pkv == pIp->pkv;
      loop invariant \forall integer j; 0 <= j < 10 ==> pIp->pkv[j] == \at(pIp->pkv[j], Pre);
      loop assigns i, chksum;
    */
    for (; i < pIp->len; i++)
    {
        chksum = chksum + pIp->pkv[i];
    }

    pIp->chksum = chksum;

    /*@ assert chksum >= 0; */
    
    return;
}
