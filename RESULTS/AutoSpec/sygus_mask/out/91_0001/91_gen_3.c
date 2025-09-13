
int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y >= 0;
    loop invariant y == x * (y / x + 1);
    loop invariant x >= 0;
    loop assigns y;
    loop assigns x;
    */
    while(y >= 0){
        y = y + x;
    }


}
