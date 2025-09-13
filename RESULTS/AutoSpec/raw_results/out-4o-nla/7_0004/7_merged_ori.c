
/*@ requires x >= 1;
    requires y >= 1;
*/
int main7(int x,int y){
  
  int a,b,p,q,r,s;

  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant y * q - x * p == a;
  loop invariant x >= 1 && y >= 1;
  loop invariant x * s - y * r == b;
  loop invariant r * x + s * y == b;
  loop invariant p * x + q * y == a;
  loop invariant p * s - q * r == 1;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant b == gcd(x, y);
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x*p + y*r;
  loop invariant a == x * p + y * r;
  loop invariant a == gcd(x, y);
  loop invariant a <= \old(a) && b <= \old(b);
  loop invariant a + b <= x + y;
  loop invariant a != b ==> a > 0 && b > 0;
  loop invariant a != b ==> \exists integer k; k > 0 && (a == x*p + y*r || b == x*q + y*s);
  loop invariant \gcd(a, b) == \gcd(x, y);
  loop invariant \exists integer k; k >= 0 && a + b == k;
  loop invariant \exists integer k; b == y - k * a;
  loop invariant \exists integer k; a == x - k * b;
  loop invariant \exists integer k; (a == b*k || b == a*k);
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop assigns s;
  loop assigns r;
  loop assigns q;
  loop assigns p;
  loop assigns b;
  loop assigns a;
  */
  while(a!=b){
      if (a>b) {
         a = a-b;
         p = p-q;
         r = r-s;
      }
      else {
         b = b-a;
         q = q-p;
         s = s-r;
      }
  }

  //@ assert(b == x*q + y*s);
}