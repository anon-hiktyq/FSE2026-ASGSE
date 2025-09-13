/*@
requires x>=1 && y>=1;
*/
void main13(int x,int y){
   
    int a=x;
    int b=y;
    int p=1;
    int q=0;

    // loop body
    /*@
    loop invariant x >= a && y >= b;
    loop invariant x * y == q + a * b * p;
    loop invariant x * y == a * b * p + q;
    loop invariant x * y == (a * b * p / (p * p)) + q;
    loop invariant q == x * y - a * b * p;
    loop invariant q == (x - a) * (y - b) * p;
    loop invariant q == (x - a) * (y - b) * p / (p / 4);
    loop invariant q == (x - a) * (y - b) * p / (p * p);
    loop invariant q + a * p + b * p == x * y;
    loop invariant q + a * b * p == x * y;
    loop invariant q + a * b * p == \old(x) * \old(y);
    loop invariant p == \pow(2, (\old(x) - a + \old(y) - b));
    loop invariant p == 2^(x - a + y - b);
    loop invariant a >= 0 && b >= 0;
    loop invariant a == 0 || b == 0 || (a % 2 == 0 || b % 2 == 0 || (a % 2 == 1 && b % 2 == 1));
    loop invariant a <= x && b <= y;
    loop invariant 1 <= p;
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
