/*@
requires a >= 0 && b >= 0;
*/
int main14(int a,int b){
   
    int x=a;
    int y=b;
    int z=0;

    // loop body
    /*@
    loop invariant z == a * b - x * y;
    loop invariant z + x*y == a*b;
    loop invariant z + x * y == a * b;
    loop invariant y <= b;
    loop invariant a <= x;
    loop invariant \forall integer k; 0 <= k <= y ==> (z == a * (b - y) + (x / (1 << (b - y))) * y);
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns z;
    loop assigns y;
    loop assigns x;
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
