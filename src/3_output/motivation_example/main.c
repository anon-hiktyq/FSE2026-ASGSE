


typedef struct __CheckCal
{
        int *pkv;
        int len;

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
    requires \valid(pIp->pkv + (0..pIp->len-1));
    requires \separated(pIp ,pIp->pkv + (0..pIp->len-1));
    requires pIp->len <= 10;
    requires \forall integer i; 0 <= i < pIp->len ==> 0 <= pIp->pkv[i] <= 100;
    ensures \result == sum(pIp->pkv, 0, pIp->len);
*/
int CheckCalFun(CheckCal *pIp)
{
        int i = 0;
        int chksum = 0;

        /*@
          loop invariant (0 < \at(pIp,Pre)->len) ==> (0 <= i <= \at(pIp,Pre)->len);
          loop invariant (0 < \at(pIp,Pre)->len) ==> (chksum == sum(pIp->pkv, 0, i));
          loop invariant (!(0 < \at(pIp,Pre)->len)) ==> ((chksum == 0)&&(i == 0)&&(pIp == \at(pIp,Pre))&&(\at(pIp,Pre)->pkv == \at(pIp->pkv,Pre))&&(*\at(pIp->pkv,Pre) == \at(*pIp->pkv,Pre))&&(\at(pIp,Pre)->len == \at(pIp->len,Pre)));
          loop invariant pIp == \at(pIp,Pre);
          loop invariant \at(pIp,Pre)->pkv == \at(pIp->pkv,Pre);
          loop invariant *\at(pIp->pkv,Pre) == \at(*pIp->pkv,Pre);
          loop invariant \at(pIp,Pre)->len == \at(pIp->len,Pre);
          loop invariant \forall integer k; 0 <= k < i ==> pIp->pkv[k] == \at(pIp->pkv[k],Pre);
          loop assigns i, chksum;
        */
        for (; i < pIp->len; i++)
        {
            chksum = chksum + pIp->pkv[i];
        }

        return chksum;
}
/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..pIp->len-1));
    requires \separated(pIp ,pIp->pkv + (0..pIp->len-1));
    requires pIp->len <= 10;
    requires \forall integer i; 0 <= i < pIp->len ==> 0 <= pIp->pkv[i] <= 100;
    */
    
void main(CheckCal *pIp)
{

    pIp->len = 3;
    int chksum = CheckCalFun(pIp);
    /*@ assert chksum == pIp->pkv[0] + pIp->pkv[1] + pIp->pkv[2]; */

}