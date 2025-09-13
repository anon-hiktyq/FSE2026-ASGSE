
void goo6(){
    int i=0;

    /*@
      requires \true;
      assigns i;
      ensures i == 30;
    */

    /*@
      loop invariant 0 <= i <= 30;
      loop assigns i;
      loop variant 30 - i;
    */
    while (i<30){
        ++i;
    }
}
