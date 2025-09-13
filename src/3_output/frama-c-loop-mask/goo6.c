
void goo6(){
    int i=0;

    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant 0 <= i <= 30;
      loop invariant i == \at(i, Pre) + (i - 0);
    */
    while (i<30){
        ++i;
    }
}
