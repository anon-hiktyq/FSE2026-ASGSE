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
  loop invariant a == b || a != b;
  loop invariant a > b ==> (a - b >= 1);
  loop invariant b > a ==> (b - a >= 1);
  loop invariant a == \old(x) - \old(y) * (\old(q) - \old(p));
  loop invariant b == \old(y) - \old(x) * (\old(s) - \old(r));
  loop invariant (r - s) * \old(y) == (q - p) * \old(x);
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