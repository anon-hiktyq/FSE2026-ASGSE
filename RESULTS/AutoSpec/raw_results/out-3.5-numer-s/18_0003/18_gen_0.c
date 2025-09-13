//svcomp_benchmark50_linear
int unknown();
/*@
  requires xa + ya > 0;
*/
void hoo18(int xa,int ya){

    //pre-condition
   
    //loop-body
    /*@
    loop invariant xa + ya == \old(xa) + \old(ya);
    loop invariant xa >= 0;
    loop invariant ya >= \old(ya);
    loop assigns xa;
    loop assigns ya;
    */
    while (xa > 0) {
        xa--;
        ya++;
    }

    //post-condition
    /*@ assert ya >= 0; */
}