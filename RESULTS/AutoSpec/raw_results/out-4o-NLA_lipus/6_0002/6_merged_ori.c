/*@ requires x >= 1;
    requires y >= 1;
*/
void main6(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant p * s - q * r == 1;
  loop invariant b == y*s + x*q;
  loop invariant b == y * s + x * q;
  loop invariant b == x*r + y*s;
  loop invariant b == x * q + y * s;
  loop invariant b == gcd(x, y);
  loop invariant b == \old(x)*q + \old(y)*s;
  loop invariant b == (x * q + y * s);
  loop invariant b == ((q * x) + (s * y));
  loop invariant b <= y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == y*r + x*p;
  loop invariant a == y * r + x * p;
  loop invariant a == x*p + y*q;
  loop invariant a == x * p + y * r;
  loop invariant a == gcd(x, y);
  loop invariant a == \old(x)*p + \old(y)*r;
  loop invariant a == (x * p + y * r);
  loop invariant a == ((p * x) + (r * y));
  loop invariant a <= x;
  loop invariant \forall integer n; a != b ==> a + b == x + y;
  loop invariant \exists integer k, l; a == x*k && b == y*l;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant (a == 1 || b == 1) ==> a == y*r + x*p;
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