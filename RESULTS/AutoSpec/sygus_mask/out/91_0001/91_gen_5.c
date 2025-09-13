
int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y >= 0;
    loop invariant y == x * i; // where i is the number of iterations
    loop assigns x;
    loop assigns y;
    */
    while(y >= 0){
        y = y + x;
    }


}
