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
  loop invariant a <= \old(a) && b <= \old(b);
  loop invariant (a == \old(a) - k * b || b == \old(b) - k * a) for some integer k >= 0;
  loop invariant \exists integer k1, k2; a == x - k1 * b && b == y - k2 * a;
  loop invariant p * \old(a) + q * \old(b) == a;
  loop invariant r * \old(a) + s * \old(b) == b;
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