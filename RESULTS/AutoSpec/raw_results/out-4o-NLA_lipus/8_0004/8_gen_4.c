/*@ requires x >= 1;
    requires y >= 1;
*/
void main8(int x,int y){
  
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
  loop invariant a >= 1 && b >= 1;
  loop invariant \forall integer k; (0 <= k < x * y) ==> (p * x + q * y == b);
  loop invariant \forall integer k; (0 <= k < x * y) ==> (r * x + s * y == a);
  loop invariant a * p + b * q == x;
  loop invariant a * r + b * s == y;
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