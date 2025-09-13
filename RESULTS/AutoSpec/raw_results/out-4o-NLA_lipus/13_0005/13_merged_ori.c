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
    loop invariant x >= 1 && y >= 1;
    loop invariant x * y == q + a * b * (p / (p / p));
    loop invariant q == x * y - a * y * p - b * x * p + a * b * p;
    loop invariant q == (x - a) * (y - b) * (p / (p / p));
    loop invariant q == (x * y) - (a * b * p);
    loop invariant q + a * p + b * p == x * y; // Tracks the product of x and y;
    loop invariant q + a * p + b * p == x * y;
    loop invariant q + a * b * p == x * y;
    loop invariant p == 2^{\min(x - a, y - b)};
    loop invariant p == 2^{\max(\log_2(x-a), \log_2(y-b)) + 1};
    loop invariant p == 1 << (2 * (\sum 0 <= i < (x - a - b))); // Tracks the power of 4 multiplier;
    loop invariant a >= 0 && b >= 0;;
    loop invariant a >= 0 && b >= 0;
    loop invariant a % 2 == 0 || b % 2 == 0;;
    loop invariant a % 2 == 0 || b % 2 == 0 || (a % 2 == 1 && b % 2 == 1);
    loop invariant a != 0 || b != 0 || q == x * y;
    loop invariant \forall integer k; k >= 0 ==> (a == 0 || b == 0 ==> q == x * y);
    loop invariant \forall integer k; 0 <= k <= x - a && 0 <= k <= y - b;
    loop invariant \forall integer k; 0 <= k <= a ==> (k * b * p + q == x * y);
    loop invariant 1 <= p;
    loop invariant 0 < p;
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
