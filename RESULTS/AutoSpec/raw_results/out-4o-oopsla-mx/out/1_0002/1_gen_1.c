int main(){
    int i=0;

    /*@
    loop invariant 0 <= i <= 30;
    loop invariant i == \at(i, Pre) + \loop_iteration;
    loop assigns i;
    */
    while (i<30){
        ++i;
    }
    //@assert i==30;
   
}