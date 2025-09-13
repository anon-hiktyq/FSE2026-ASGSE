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
  loop invariant a >= 1 && b >= 1;
  loop invariant a == b || a != b;
  loop invariant a == \old(x) - \sum integer k; 0 <= k < \at(n, Here) && \at(a, Here) > \at(b, Here) : \at(b, Here);
  loop invariant b == \old(y) - \sum integer k; 0 <= k < \at(n, Here) && \at(b, Here) > \at(a, Here) : \at(a, Here);
  loop invariant \old(x) * s + \old(y) * (-r) == a;
  loop invariant \old(x) * (-q) + \old(y) * p == b;
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