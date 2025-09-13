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
  loop invariant y == a * r + b * s;
  loop invariant x >= a && y >= b;
  loop invariant x == a * p + b * q;
  loop invariant r * x + s * y == y;
  loop invariant p * x + q * y == x;
  loop invariant b * p - a * q == y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == b || a != b;
  loop invariant a <= x && b <= y;
  loop invariant a + b == x + y;
  loop invariant a * s - b * r == x;
  loop invariant a % b == x % y;
  loop invariant \exists integer k; a == k * b || b == k * a;
  loop invariant (r - s) * y == (q - p) * x;
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