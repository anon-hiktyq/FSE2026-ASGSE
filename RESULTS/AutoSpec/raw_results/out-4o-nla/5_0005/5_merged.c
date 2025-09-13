/*@ requires x >= 1;
    requires y >= 1;
*/
int main5(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant q*x + s*y == b;
  loop invariant p*x + r*y == a;
  loop invariant p*s - r*q == 1;
  loop invariant p * s - r * q == 1;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant b == \abs(q * x - s * y);
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 1 && b >= 1 && p*q == s*q;
  loop invariant a == x*p + y*r;
  loop invariant a == x * p + y * r;
  loop invariant a == \abs(p * x - r * y);
  loop invariant a + b <= x + y;
  loop invariant a * s - b * r == y;
  loop invariant a * q - b * p == x;
  loop invariant a != b ==> a > 0 && b > 0;
  loop invariant a != b ==> \abs(p*s - r*q) == 1;
  loop invariant \forall integer k; 1 <= k <= x + y ==> p*s - r*q == 1;
  loop invariant \exists integer k, l; a == k*x - l*y && b == l*x - k*y;
  loop invariant 1 == p*s - r*q;
  loop invariant 1 == p * s - r * q;
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
 
  //@ assert(1 == p*s - r*q);
}
