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
  loop invariant r * \old(a) + s * \old(b) == b;
  loop invariant p * y - q * x == r * y - s * x;
  loop invariant p * y + q * x == r * y + s * x;
  loop invariant p * s - q * r == 1;
  loop invariant p * \old(a) + q * \old(b) == a;
  loop invariant b == x * q + y * s;
  loop invariant b == \old(b) - \sum(0 <= i < \at(b, Pre)) (b > a ? \at(a, LoopEntry) : 0);
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x * p + y * r;
  loop invariant a == b || a != b;
  loop invariant a == \old(a) - \sum(0, k, \lambda i; p) && b == \old(b) - \sum(0, k, s);
  loop invariant a == \old(a) - \sum(0 <= i < \at(a, Pre)) (a > b ? \at(b, LoopEntry) : 0);
  loop invariant a <= x && b <= y;
  loop invariant a <= \old(a) && b <= \old(b);
  loop invariant a + b == x + y;
  loop invariant a + b <= x + y;
  loop invariant a * s - b * r == x;
  loop invariant a * q - b * p == y;
  loop invariant \exists integer k; a == b + k * (x - y) || b == a + k * (y - x);
  loop invariant \exists integer k1, k2; a == x - k1 * b && b == y - k2 * a;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (r * \old(x) + s * \old(y)) == b;
  loop invariant (q * y + s * x == x * y);
  loop invariant (p * y - q * x) == (r * x - s * y);
  loop invariant (p * y + r * x == x * y);
  loop invariant (p * \old(x) + q * \old(y)) == a;
  loop invariant (a == \old(a) - k * b || b == \old(b) - k * a) for some integer k >= 0;
  loop assigns s;
  loop assigns r;
  loop assigns q;
  loop assigns p;
  loop assigns b;
  loop assigns a;
  ```c;
  ```;
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