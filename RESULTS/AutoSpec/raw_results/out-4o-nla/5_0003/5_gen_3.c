/*@ requires x >= 1;
    requires y >= 1;
*/
int main5(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant a >= 1 && b >= 1;
  loop invariant \exists integer k1, k2; a == k1 * x - k2 * y && b == k2 * x - k1 * y;
  loop invariant p * s - r * q == 1;
  loop invariant a == p * x + r * y;
  loop invariant b == q * x + s * y;
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
 
  //@ assert(1 == p*s - r*q);
}
