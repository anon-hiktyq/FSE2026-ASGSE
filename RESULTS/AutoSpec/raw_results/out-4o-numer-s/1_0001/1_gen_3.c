//svcomp_css2003
int unknown();
/*@
  requires k >= 0;
  requires k <= 1;
*/
void hoo1(int k){
    int i = 1;
    int j = 1;

    //pre-condition
 

    //loop-body
    /*@
    loop invariant i >= 1;
    loop invariant j >= 1;
    loop invariant k >= 0;
    loop invariant k <= 1;
    loop invariant i + k <= 2;
    loop assigns i;
    loop assigns j;
    loop assigns k;
    */
    while (unknown()) {
        i = i + 1;
        j = j + k;
        k = k - 1;
    }

    //post-condition
    /*@ assert i + k <= 2; */
}