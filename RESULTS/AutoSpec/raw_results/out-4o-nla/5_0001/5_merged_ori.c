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
  loop invariant y == a * r + b * s;
  loop invariant x*r + b*s == y;
  loop invariant x*p + b*q == x;
  loop invariant x == a * p + b * q;
  loop invariant p * s - r * q == 1;
  loop invariant b == y - x*r + a*s;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant b <= y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x*p + y*r;
  loop invariant a == x - p * b && b == y - q * a;
  loop invariant a == x - b*p + y*q;
  loop invariant a == x * p + y * r;
  loop invariant a == b ==> a == (x % y) + (y % x);
  loop invariant a == b ==> (p * s - r * q == 1);
  loop invariant a <= x;
  loop invariant a != b ==> (p * s - r * q == 1);
  loop invariant \forall integer k; (a == x - k * b) && (b == y - k * a);
  loop invariant \exists integer k, l, m, n; a == k * x + l * y && b == m * x + n * y && 1 == p*s - r*q;
  loop invariant 1 == p*s - r*q;
  loop invariant 1 == p * s - r * q;
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
 
  //@ assert(1 == p*s - r*q);
}
