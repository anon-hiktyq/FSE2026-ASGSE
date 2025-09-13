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
    loop invariant x*y == a*b*p + q;
    loop invariant q == x*y - a*b*p;
    loop invariant q == x * y - a * b * p;
    loop invariant q == (x - a) * (y - b) * p / 4 + (x * y - (x - a) * (y - b));
    loop invariant p == 2^(number of times both a and b were halved);
    loop invariant p == 2^(number of divisions by 2 applied to both a and b);
    loop invariant b % 2 == 0 ==> p % 2 == 0;
    loop invariant a >= 0 && b >= 0;
    loop invariant a == 0 || b == 0 || a % 2 == 1 || b % 2 == 1 || a % 2 == 0 && b % 2 == 0;
    loop invariant a % 2 == 0 ==> p % 4 == 0;
    loop invariant \forall integer k; 0 <= k <= x && 0 <= k <= y ==> a <= x && b <= y;
    loop invariant \forall integer k; 0 <= k < p ==> k % 4 == 0;
    loop invariant \exists integer k, m; a == x - k && b == y - m && k >= 0 && m >= 0;
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
