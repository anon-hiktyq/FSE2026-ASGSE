int main(){
    int i=0;

    /*@
    loop invariant i == \at(i, Pre) + \loop_iteration;
    loop invariant i <= 30;
    loop invariant \at(i, Here) <= 30;
    loop invariant 30 - i;
    loop invariant 0 <= i;
    loop assigns i;
    */
    while (i<30){
        ++i;
    }
    //@assert i==30;
   
}