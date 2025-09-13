
/*@
    requires k >= 0;
    requires k <= 1;
*/
int hoo1(int k){
    int i = 1;
    int j = 1;

    //pre-condition
    /*@ assert j == 1; */
    /*@ assert i == 1; */
    /*@ assert k == \at(k, Pre); */

    //loop-body
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
        loop invariant k <= \at(k, Pre);
        loop invariant i >= 1;
        loop invariant i + k <= 2;
        loop assigns i, j, k;
    */
    while (unknown()) {
        i = i + 1;
        j = j + k;
        k = k - 1;
    }

    //post-condition
    /*@ assert i + k <= 2; */
}
