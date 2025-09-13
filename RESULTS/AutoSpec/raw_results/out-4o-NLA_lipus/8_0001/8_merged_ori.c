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
  loop invariant x * y == (p * s - q * r) * a;
  loop invariant b == y - (r * b) + (s * a);
  loop invariant b == q * x + s * y;
  loop invariant b == \old(y) - \sum integer k; 0 <= k < \at(n, Here) && \at(b, Here) > \at(a, Here) : \at(a, Here);
  loop invariant b == (r * x) + (s * y);
  loop invariant a >= b || b >= a;
  loop invariant a >= b && p >= q && r >= s || b > a && q >= p && s >= r;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x - (p * b) + (q * a);
  loop invariant a == p * x + r * y;
  loop invariant a == b || a != b;
  loop invariant a == \old(x) - \sum integer k; 0 <= k < \at(n, Here) && \at(a, Here) > \at(b, Here) : \at(b, Here);
  loop invariant a == (p * x) + (q * y);
  loop invariant a * s + b * r == y;
  loop invariant a * s + b * r == x;
  loop invariant a * q + b * p == y;
  loop invariant a * q + b * p == x;
  loop invariant a != b;
  loop invariant a != b ==> a > 0 && b > 0;
  loop invariant \old(x) * s + \old(y) * (-r) == a;
  loop invariant \old(x) * (-q) + \old(y) * p == b;
  loop invariant \gcd(a, b) == \gcd(x, y);
  loop invariant \forall integer k; y == a * r + b * s;
  loop invariant \forall integer k; x == a * p + b * q;
  loop invariant \exists integer k; b == k * q * y;
  loop invariant \exists integer k; a == k * p * x;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (r-s) * y == (q-p) * x;
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (a != b) ==> ((r - s) * y == (q - p) * x);
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