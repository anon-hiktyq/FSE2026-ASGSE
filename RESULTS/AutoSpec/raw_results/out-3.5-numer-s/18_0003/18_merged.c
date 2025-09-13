//svcomp_benchmark50_linear
int unknown();
/*@
  requires xa + ya > 0;
*/
void hoo18(int xa,int ya){

    //pre-condition
   
    //loop-body
    /*@
    loop assigns ya;
    loop assigns xa;
    */
    while (xa > 0) {
        xa--;
        ya++;
    }

    //post-condition
}