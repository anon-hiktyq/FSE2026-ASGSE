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
  loop invariant r * y == q * x;
  loop invariant p * s - q * r == 1;
  loop invariant b == x * q + y * s;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x * p + y * r;
  loop invariant a == b || a != b;
  loop invariant a <= x && b <= y;
  loop invariant a + b == x + y;
  loop invariant a + b <= x + y;
  loop invariant a * s - b * r == x;
  loop invariant \exists integer k; a == b + k * (x - y) || b == a + k * (y - x);
  loop invariant \exists integer k1, k2; a == x - k1 * b && b == y - k2 * a;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (p * y + r * x == x * y);
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