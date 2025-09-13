/*@ requires x >= 1;
    requires y >= 1;
*/
int main8(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant r - s == q - p;
  loop invariant b > a ==> (b - a >= 1);
  loop invariant b == y - (r * y - s * x);
  loop invariant b == x*q + y*s;
  loop invariant b == r*x + s*y;
  loop invariant b == q*x + s*y;
  loop invariant b == \old(y) - \old(x) * (\old(s) - \old(r));
  loop invariant b == \old(b) - x*s + y*r;
  loop invariant b <= y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a > b ==> (a - b >= 1);
  loop invariant a > 0 && b > 0;
  loop invariant a == x*p + y*r;
  loop invariant a == x - b*(q-p) && b == y - a*(r-s);
  loop invariant a == x - (p * y - q * x);
  loop invariant a == p*x + r*y;
  loop invariant a == p*x + q*y;
  loop invariant a == b || a != b;
  loop invariant a == \old(x) - \old(y) * (\old(q) - \old(p));
  loop invariant a == \old(a) - x*q + y*p;
  loop invariant a <= x;
  loop invariant a - b == (p - q) * x + (r - s) * y;
  loop invariant a != b;
  loop invariant \exists integer m; b == y - m*a && q == 1 - m*p && s == -m*r;
  loop invariant \exists integer k; a == x - k*b && p == 1 - k*q && r == -k*s;
  loop invariant \exists integer k; a == k*x + b == k*y;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant (r-s) * y == (q-p) * x;
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (r - s) * \old(y) == (q - p) * \old(x);
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
 
  //@ assert((r-s) * y == (q-p) * x);
}