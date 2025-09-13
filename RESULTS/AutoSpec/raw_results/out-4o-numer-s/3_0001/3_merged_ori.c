//svcomp_const
int unknown();
void hoo3() {
    //pre-condition
    int s = 0;

    //loop-body
    /*@
    loop invariant s > 0 ==> \exists integer k; 0 <= k < \at(s, Pre) && unknown() == 1;
    loop invariant s == 0 || s >= 1;
    loop invariant s == 0 || s > 0;
    loop invariant s == 0 || \forall integer k; 0 <= k < s ==> k >= 0;
    loop invariant s == 0 ==> \forall integer k; 0 <= k < \at(s, Pre) ==> unknown() == 0;
    loop invariant s == 0 ==> \forall integer k; 0 <= k < \at(s, Pre) ==> s == 0;
    loop invariant s != 0 ==> s > 0;
    loop invariant s != 0 ==> (\exists integer k; 0 <= k < \at(s, Pre) && k + \at(s, Pre) == s);
    loop invariant \forall integer k; 0 <= k < s ==> s == 0;
    loop invariant \forall integer k; 0 <= k < s ==> k >= 0;
    loop invariant 0 <= s;
    loop assigns s;
    */
    while(unknown()){
        if (s != 0){
            s = s + 1;
        }
    }

    //post-condition
    /*@ assert s == 0; */

}