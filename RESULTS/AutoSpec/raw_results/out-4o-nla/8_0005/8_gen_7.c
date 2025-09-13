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
  loop invariant a >= 1 && b >= 1;
  loop invariant a == \old(a) - \sum(0 <= i < \at(a, Pre)) (a > b ? \at(b, LoopEntry) : 0);
  loop invariant b == \old(b) - \sum(0 <= i < \at(b, Pre)) (b > a ? \at(a, LoopEntry) : 0);
  loop invariant (p * \old(x) + q * \old(y)) == a;
  loop invariant (r * \old(x) + s * \old(y)) == b;
  loop invariant p * s - q * r == 1;
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