//svcomp_benchmark50_linear
int unknown();
/*@
  requires xa + ya > 0;
*/
void hoo18(int xa,int ya){

    //pre-condition
   
    //loop-body
    /*@
    loop invariant xa + ya == \at(xa + ya,Pre);
    loop invariant xa + ya == \at(xa + ya, Pre);
    loop invariant \old(xa + ya) == xa + ya;
    loop invariant \forall integer k; xa >= 0 ==> ya >= 0;
    loop invariant \forall integer k; 0 <= k ==> ya >= 0;
    loop invariant \exists integer k; k >= 0 && xa + ya == k;
    loop invariant \at(ya,Pre) <= ya;
    loop invariant 0 <= ya;
    loop invariant 0 <= xa;
    loop invariant 0 < xa + ya;
    loop assigns ya;
    loop assigns xa;
    */
    while (xa > 0) {
        xa--;
        ya++;
    }

    //post-condition
    /*@ assert ya >= 0; */
}