/*@ requires x >= 1;
    requires y >= 1;
*/
void main8(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant x * s - y * p == a;
  loop invariant x * r - y * q == b;
  loop invariant s * y == p * x;
  loop invariant r * y == q * x;
  loop invariant r * b + s * a == y;
  loop invariant p * b + q * a == x;
  loop invariant b >= a ==> \exists integer k; b == y - k*x;
  loop invariant b == y - x * (q - r);
  loop invariant b == y - q * a - s * x;
  loop invariant b == x*q + y*s;
  loop invariant a >= b ==> \exists integer k; a == x - k*y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == x*p + y*r;
  loop invariant a == x - y * (p - q);
  loop invariant a == x - p * b - r * y;
  loop invariant a <= x && b <= y;
  loop invariant a + b == x + y;
  loop invariant a != b ==> a > 0 && b > 0;
  loop invariant \forall integer u, v; u >= 1 && v >= 1 ==> \exists integer k; u == x - k*v || v == y - k*u;
  loop invariant \exists integer k; a == k * b || b == k * a;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (r-s) * y == (q-p) * x;
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (p - q) * b + (r - s) * a == x * y;
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