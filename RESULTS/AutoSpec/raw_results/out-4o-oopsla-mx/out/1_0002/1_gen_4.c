int main(){
    int i=0;

    /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
    loop invariant \at(i, Here) <= 30;
    */
    while (i<30){
        ++i;
    }
    //@assert i==30;
   
}