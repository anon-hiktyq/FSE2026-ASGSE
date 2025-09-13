/*@ requires x >= 1;
    requires y >= 1;
*/
int main6(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant y == a*r + b*s;
  loop invariant x == a*p + b*q;
  loop invariant b == y*s + x*q;
  loop invariant b == x*r + y*s;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant b == gcd(x, y);
  loop invariant b == a*x + (x-y)*q;
  loop invariant a >= 1 || b >= 1;
  loop invariant a >= 1 && b >= 1;
  loop invariant a > 0 && b > 0;
  loop invariant a == y*r + x*p;
  loop invariant a == x*p + y*r;
  loop invariant a == x*p + y*q;
  loop invariant a == x * p + y * r;
  loop invariant a == gcd(x, y);
  loop invariant a == b*y + (x-y)*p;
  loop invariant a == b*x*s + y*p;
  loop invariant a == b*x*r + y*q;
  loop invariant a == b || a > 0 && b > 0;
  loop invariant a == b || a != b;
  loop invariant a + b == x + y;
  loop invariant a + b == x * (p + q) + y * (r + s);
  loop invariant \exists integer k; b == a + k*x && q == k*p && s == k*r;
  loop invariant \exists integer k; a == b + k*y && p == k*q && r == k*s;
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
 
  //@ assert(a == y*r + x*p);
 
}