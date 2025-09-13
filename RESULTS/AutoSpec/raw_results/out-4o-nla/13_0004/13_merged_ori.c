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
    loop invariant x >= a && y >= b;
    loop invariant x * y == q + a * b * p;
    loop invariant x * y == a * b * p + q;
    loop invariant q == x*y - a*b*p;
    loop invariant q == x * y - a * b * p;
    loop invariant q == (x - a) * (y - b) * p / (p / 4) / (p / 4);
    loop invariant q == (x - a) * (y - b) * p / (p / (4 ^ ((x - a) + (y - b))));
    loop invariant q + a * p + b * p == x * y;
    loop invariant p == 2^(number of divisions by 2 applied to both a and b);
    loop invariant p == 2^(initial_a - a + initial_b - b); // where initial_a and initial_b are the initial values of a and b;
    loop invariant p == 2^(\count(a % 2 == 0 && b % 2 == 0));
    loop invariant a >= 0 && b >= 0;
    loop invariant a == 0 || b == 0 || (a % 2 == 0 || b % 2 == 0 || a % 2 == 1 && b % 2 == 1);
    loop invariant \forall integer k; p == 2^(2*k) && k >= 0;
    loop invariant 1 <= p;
    loop invariant 0 <= a * b;
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
