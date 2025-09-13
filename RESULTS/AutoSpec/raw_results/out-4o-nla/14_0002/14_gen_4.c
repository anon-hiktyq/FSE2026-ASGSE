/*@
requires a >= 0 && b >= 0;
*/
int main14(int a,int b){
   
    int x=a;
    int y=b;
    int z=0;

    // loop body
    /*@
    loop invariant x == 2^(original_y - \floor(y)) * a;
    loop invariant z == (original_y - y) * a + \floor(y / 2) * a * 2;
    loop invariant y >= 0;
    loop assigns x, y, z;
    */
    while(y!=0) {
     
     if (y%2 ==1 ){
          z = z+x;
          y = y-1;
     }
     x = 2*x;
     y = y/2;
    }

    // @ assert z == a*b;
}
