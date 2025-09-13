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
  loop invariant y * p - x * q == b * (p - q);
  loop invariant x * s - y * r == a * (s - r);
  loop invariant a >= 1 && b >= 1;
  loop invariant a == b || (a > 0 && b > 0);
  loop invariant a <= x && b <= y;
  loop invariant a + b == x + y;
  loop invariant a * s - b * r == y;
  loop invariant \exists integer k; a == x - k * b || b == y - k * a;
  loop invariant \exists integer k; a == k * b || b == k * a;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (r - s) * y == (q - p) * x;
  loop invariant (p * b + q * a == x) && (r * b + s * a == y);
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