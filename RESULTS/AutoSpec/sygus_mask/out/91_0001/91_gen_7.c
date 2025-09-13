
int main(){

    int x = 0;
    int y = 0;

    /*@
    loop invariant y >= 0;
    loop invariant y == x * (1 + \floor{y/x});
    loop assigns y;
    loop assigns x;
    */
    while(y >= 0){
        y = y + x;
    }


}
