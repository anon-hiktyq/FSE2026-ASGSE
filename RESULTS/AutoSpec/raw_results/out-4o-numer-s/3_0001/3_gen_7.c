//svcomp_const
int unknown();
void hoo3() {
    //pre-condition
    int s = 0;

    //loop-body
    /*@
    loop invariant s == 0 || s > 0;
    loop invariant s == 0 ==> \forall integer k; 0 <= k < \at(s, Pre) ==> s == 0;
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