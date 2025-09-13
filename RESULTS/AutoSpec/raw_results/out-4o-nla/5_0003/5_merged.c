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
  loop invariant x * s + y * r == b;
  loop invariant x * q + y * p == a;
  loop invariant p * s - r * q == 1;
  loop invariant b == x * q + y * s;
  loop invariant b == q * x + s * y;
  loop invariant a >= b || b >= a;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x * p + y * r;
  loop invariant a == p * x + r * y;
  loop invariant a <= x && b <= y;
  loop invariant a * s + b * q == y;
  loop invariant a * r + b * p == x;
  loop invariant a != b ==> a > 0 && b > 0;
  loop invariant \exists integer k; k >= 0 && b == y - k * a;
  loop invariant \exists integer k; k >= 0 && a == x - k * b;
  loop invariant \exists integer k; a == x - k * b || b == y - k * a;
  loop invariant \exists integer k1, k2; a == k1 * x - k2 * y && b == k2 * x - k1 * y;
  loop invariant 1 == p * s - r * q;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (y == a * r + b * s);
  loop invariant (x == a * p + b * q);
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
