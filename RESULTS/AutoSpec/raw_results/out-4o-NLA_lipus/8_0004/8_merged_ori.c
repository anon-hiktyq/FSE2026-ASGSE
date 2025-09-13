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
  loop invariant x > 0 && y > 0;
  loop invariant x * r + y * p == x && y * s + x * q == y;
  loop invariant q * a + s * b == y;
  loop invariant p * b + r * a == x;
  loop invariant b == y - (r-s) * a;
  loop invariant b == y - (r * b + s * a);
  loop invariant b == y - (r * a + s * b);
  loop invariant b == y - (q * a + s * b);
  loop invariant a*y*s == b*x*q;
  loop invariant a*x*r == b*y*p;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a > 0 && b > 0;
  loop invariant a == x - (p-q) * b;
  loop invariant a == x - (p*q) && b == y - (r*s);
  loop invariant a == x - (p * b + r * a);
  loop invariant a == x - (p * b + q * a);
  loop invariant a == b || \forall integer k; 0 <= k < a ==> a - b == k || b - a == k;
  loop invariant a * r + b * s == y;
  loop invariant a * p + b * q == x;
  loop invariant a * (s + q) == b * (r + p);
  loop invariant \forall integer k; 0 <= k <= y <==> b >= 1;
  loop invariant \forall integer k; 0 <= k <= x <==> a >= 1;
  loop invariant \forall integer k; 0 <= k < a ==> a >= b || b > a;
  loop invariant \forall integer k; (0 <= k < x * y) ==> (r * x + s * y == a);
  loop invariant \forall integer k; (0 <= k < x * y) ==> (p * x + q * y == b);
  loop invariant \abs(r * y - q * x) == \abs(s * y - p * x);
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (x * s) + (y * r) == (x * q) + (y * p);
  loop invariant (r-s) * y == (q-p) * x;
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (q-p)*x == (r-s)*y;
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