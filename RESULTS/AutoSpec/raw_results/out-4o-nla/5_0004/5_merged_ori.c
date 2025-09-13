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
  loop invariant x >=1 && y >=1;
  loop invariant q*x + s*y == b;
  loop invariant p*x + r*y == a;
  loop invariant p*s - r*q ==1;
  loop invariant p * s - r * q == 1;
  loop invariant b == y * q - x * p;
  loop invariant b == x * q + y * s;
  loop invariant b == \old(x) * q + \old(y) * p;
  loop invariant b <= y;
  loop invariant a >= 1 && b >=1;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x * s - y * r;
  loop invariant a == x * p + y * r;
  loop invariant a == \old(x) * s + \old(y) * r;
  loop invariant a <= x;
  loop invariant a + b == x + y;
  loop invariant \forall integer k; a == b ==> (p * s - r * q == 1);
  loop invariant \exists integer k; a == k*x - (k-1)*y || b == k*y - (k-1)*x;
  loop invariant =b < a;
  loop invariant 1 == p*s - r*q;
  loop invariant 1 == p * s - r * q;
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
 
  //@ assert(1 == p*s - r*q);
}
