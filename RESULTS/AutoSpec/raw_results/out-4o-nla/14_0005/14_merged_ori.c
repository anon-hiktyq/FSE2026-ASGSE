/*@
requires a >= 0 && b >= 0;
*/
int main14(int a,int b){
   
    int x=a;
    int y=b;
    int z=0;

    // loop body
    /*@
    loop invariant z == a * (b - y);
    loop invariant z + x*y == a*b;
    loop invariant z + x * y == a * b;
    loop invariant x >= 0 && y >= 0 && z >= 0;
    loop invariant x == a * pow(2, \floor(log2(b + 1 - y)));
    loop invariant a >= 0 && b >= 0;
    loop invariant a <= x;
    loop invariant \forall integer t; y % 2 == 0 && t <= y ==> (z == a*b - t*x);
    loop invariant 0 <= z;
    loop invariant 0 <= y;;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant (y % 2 == 0 || z >= x);
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
