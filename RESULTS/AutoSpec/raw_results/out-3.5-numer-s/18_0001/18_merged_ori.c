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
    loop invariant \old(ya) <= ya;
    loop invariant 0 <= xa;
    loop assigns ya;
    loop assigns xa;
    ```c;
    ```;
    Looking at this function, I need to analyze what happens in the loop and what properties are preserved throughout the iterations.;
    */
    while (xa > 0) {
        xa--;
        ya++;
    }

    //post-condition
    /*@ assert ya >= 0; */
}