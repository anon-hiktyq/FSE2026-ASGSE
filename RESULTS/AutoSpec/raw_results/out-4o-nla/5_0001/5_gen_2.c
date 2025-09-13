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
  loop invariant \forall integer k; (a == x - k * b) && (b == y - k * a);
  loop invariant a == x - p * b && b == y - q * a;
  loop invariant p * s - r * q == 1;
  loop invariant a == b ==> a == (x % y) + (y % x);
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
