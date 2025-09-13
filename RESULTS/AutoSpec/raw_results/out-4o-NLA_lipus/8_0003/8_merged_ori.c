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
  loop invariant q * x + s * y == b;
  loop invariant p * x + r * y == a;
  loop invariant b == y - a*(r-s) - b*(s-r);
  loop invariant b == y - (r*s) * (y/x);
  loop invariant b == y - (r * b + s * a);
  loop invariant b == \old(y) - (q * \old(x) + s * \old(y));
  loop invariant b == \old(b) - \old(a) * (p-q) + \old(y) * (s-r);
  loop invariant b <= y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == x - b*(p-q) - a*(q-p);
  loop invariant a == x - (p*q) * (x/y);
  loop invariant a == x - (p * b + q * a);
  loop invariant a == \old(x) - (p * \old(x) + r * \old(y));
  loop invariant a == \old(a) - \old(b) * (q-p) + \old(x) * (r-s);
  loop invariant a <= x;
  loop invariant a + b == x + y;
  loop invariant a * s == b * r;
  loop invariant a * q == b * p;
  loop invariant \forall integer k; 0 <= k < y ==> b <= y;
  loop invariant \forall integer k; 0 <= k < x ==> a <= x;
  loop invariant \exists integer k; a == k * b || b == k * a;
  loop invariant \abs(r*s - q*p) == 1;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant (x * r) - (y * p) == (x * s) - (y * q);
  loop invariant (r-s) * y == (q-p) * x;
  loop invariant (r-s) * \old(y) == (q-p) * \old(x);
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (r - s) * \old(y) == (q - p) * \old(x);
  loop invariant (p * x + r * y) == (s * y + q * x);
  loop invariant ((r-s) * y) == ((q-p) * x);
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