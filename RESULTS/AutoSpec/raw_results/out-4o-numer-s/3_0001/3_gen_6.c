//svcomp_const
int unknown();
void hoo3() {
    //pre-condition
    int s = 0;

    //loop-body
    /*@
    loop invariant s == 0 || s >= 1;
    loop invariant \forall integer k; 0 <= k < s ==> s == 0;
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