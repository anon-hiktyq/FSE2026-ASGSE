/*@
requires x>=1 && y>=1;
*/
int main13(int x,int y){
   
    int a=x;
    int b=y;
    int p=1;
    int q=0;

    // loop body
    /*@
    loop invariant x*y == a*b*p + q;
    loop invariant x * y == a * b * p + q;
    loop invariant q == x*y - a*b*p;
    loop invariant q == x * y - (2^(p/4) * a + 2^(p/4) * b + (a + b) / 2) * p;
    loop invariant q == (x - a) * (y - b) * p;
    loop invariant q + a * b * p == x * y;
    loop invariant b % 2 == 0 ==> q % 2 == 0;
    loop invariant b % 2 == 0 ==> q % (2 * p) == (x * y) % (2 * p);
    loop invariant a >= 0 && b >= 0;
    loop invariant a * y + b * x - a * b == x * y - q;
    loop invariant a * b == 0 ==> q == x * y;
    loop invariant a % 2 == 0 || b % 2 == 0;
    loop invariant a % 2 == 0 || b % 2 == 0 || a % 2 == 1 && b % 2 == 1;
    loop invariant a % 2 == 0 ==> q % 2 == 0;
    loop invariant a % 2 == 0 ==> q % (2 * p) == (x * y) % (2 * p);
    loop invariant \forall integer j; 0 <= j < x ==> q >= j * y;
    loop invariant 1 <= p;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant 0 < p;
    loop invariant (a == 0 || b == 0) ==> q == x * y;
    loop assigns q;
    loop assigns p;
    loop assigns b;
    loop assigns a;
    */
    while(a!=0 && b!=0) {
     if (a % 2 ==0 && b % 2 ==0 ){
          a = a/2;
          b = b/2;
          p = 4*p;
     }
     else if (a % 2 ==1 && b % 2 ==0 ){
          a = a-1;
          q = q+b*p;
     }
     else if (a % 2 ==0 && b % 2 ==1 ){
          b = b-1;
          q = q+a*p;
     }
     else {
          a = a-1;
          b = b-1;
          q = q+(a+b+1)*p;
     }
    }
    // @ assert q == x*y;
}
