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
  loop invariant a >= b ==> \exists integer k; a == x - k*y;
  loop invariant b >= a ==> \exists integer k; b == y - k*x;
  loop invariant (r-s) * y == (q-p) * x;
  loop invariant \forall integer u, v; u >= 1 && v >= 1 ==> \exists integer k; u == x - k*v || v == y - k*u;
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