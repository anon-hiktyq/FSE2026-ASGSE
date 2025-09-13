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
  loop invariant a >= 1;
  loop invariant b >= 1;
  loop invariant x >= 1;
  loop invariant y >= 1;
  loop invariant 0 <= a <= x;
  loop invariant 0 <= b <= y;
  loop invariant \exists integer k; a == k*x + b == k*y;
  loop invariant a == p*x + q*y;
  loop invariant b == r*x + s*y;
  loop invariant r - s == q - p;
  loop assigns a, b, p, q, r, s;
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