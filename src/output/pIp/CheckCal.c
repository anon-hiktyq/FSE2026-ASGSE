
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
    requires \valid(pIp);                          // Pointer validity
    requires \valid(pIp->pkv + (0..pIp->len-1));   // Array bounds for pkv
    requires 0 <= pIp->len <= 10;                  // Length constraint
    requires \forall integer i; 0 <= i < pIp->len ==> \valid(pIp->pkv + i); // Validity of each element in pkv
    requires \forall integer i; 0 <= i < pIp->len ==> 0 <= pIp->pkv[i] && pIp->pkv[i] <= 100; // Element bounds
    assigns pIp->chksum;                           // Function modifies chksum
    ensures \valid(pIp);                           // Ensure pointer validity remains
    ensures \valid(pIp->pkv + (0..pIp->len-1));    // Ensure array bounds remain valid
    ensures pIp->chksum == sum(pIp->pkv, 0, pIp->len); // Checksum correctness
*/
void CheckCal(CheckCal *pIp)
{
    int i = 0;
    int chksum = 0;

    /*@ 
        loop invariant \valid(pIp);                              // Pointer validity
        loop invariant \valid(pIp->pkv + (0..pIp->len-1));       // Array bounds for pkv
        loop invariant 0 <= pIp->len <= 10;                      // Length constraint
        loop invariant \forall integer j; 0 <= j < pIp->len ==> 0 <= pIp->pkv[j] && pIp->pkv[j] <= 100; // Element bounds
        loop invariant 0 <= i <= pIp->len;                       // Loop index bounds
        loop invariant chksum == sum(pIp->pkv, 0, i);            // Partial sum correctness
        loop assigns i, chksum;                                  // Variables modified in the loop
        loop variant pIp->len - i;                               // Loop variant for termination
    */
    for (; i < pIp->len; i++)
    {
        chksum = chksum + pIp->pkv[i];
    }

    /*@ assert pIp->len == \at(pIp->len, Pre); */                // Ensure len is unchanged
    /*@ assert pIp->chksum == \at(pIp->chksum, Pre); */          // Ensure chksum is unchanged before assignment

    pIp->chksum = chksum;

    return;
}
