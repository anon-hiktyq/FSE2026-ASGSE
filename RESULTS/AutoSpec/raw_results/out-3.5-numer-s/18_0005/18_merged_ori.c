//svcomp_benchmark50_linear
int unknown();
/*@
  requires xa + ya > 0;
*/
void hoo18(int xa,int ya){

    //pre-condition
   
    //loop-body
    /*@
    loop invariant 0 <= xa;
    loop invariant 0 < xa + ya;
    loop assigns ya;
    loop assigns xa;
    ```c;
    ```;
    The loop decrements `xa` and increments `ya` until `xa` reaches 0. The precondition states that `xa + ya > 0` initially.;
    Looking at this function, I need to analyze what happens in the loop and what properties are maintained throughout.;
    */
    while (xa > 0) {
        xa--;
        ya++;
    }

    //post-condition
    /*@ assert ya >= 0; */
}