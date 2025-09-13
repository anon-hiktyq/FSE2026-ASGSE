
/*@ requires x >= 1;
    requires y >= 1;
*/
int main7(int x,int y){
  
  int a,b,p,q,r,s;

  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant r >= 0 && s >= 0;
  loop invariant p*s - q*r == 1;
  loop invariant p >= 0 && q >= 0;
  loop invariant p * s - q * r == 1;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant b == q*x + s*y;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 1 && b >= 1 && b == x*q + y*s;
  loop invariant a == x*p + y*r;
  loop invariant a == x * p + y * r;
  loop invariant a == p*x + r*y;
  loop invariant a + b <= x + y;
  loop invariant a != b || (b == x*q + y*s);
  loop invariant \exists integer k, l; a == x*k + y*l && b == x*q + y*s;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
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

  //@ assert(b == x*q + y*s);
}