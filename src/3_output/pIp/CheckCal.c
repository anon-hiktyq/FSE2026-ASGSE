
typedef struct __CheckCal
{
    int len;
    int *pkv;
    int chksum;

} CheckCal;

/*@
axiomatic Sum_array {
    logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
    axiom empty:
        \forall int* a, integer b, e; b >= e ==> sum(a, b, e) == 0;
    axiom range:
        \forall int* a, integer b, e; b < e ==> sum(a, b, e) == sum(a, b, e-1) + a[e-1];
}
*/

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires pIp->len <= 10;
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] && pIp->pkv[i] <= 100;
    ensures pIp->chksum == sum(pIp->pkv, 0, pIp->len);
*/
void CheckCal(CheckCal *pIp)
{
    int i = 0;
    int chksum = 0;

    /*@ 
        loop invariant \valid(pIp);
        loop invariant \valid(pIp->pkv + (0..9));
        loop invariant pIp->len <= 10;
        loop invariant \forall integer j; 0 <= j < 10 ==> 0 <= pIp->pkv[j] && pIp->pkv[j] <= 100;
        loop assigns i, chksum;
        loop variant pIp->len - i;
    */
    for (; i < pIp->len; i++)
    {
        chksum = chksum + pIp->pkv[i];
    }

    /*@ assert pIp->len == \at(pIp->len, Pre); */
    /*@ assert pIp->chksum == \at(pIp->chksum, Pre); */

    pIp->chksum = chksum;

    return;
}
