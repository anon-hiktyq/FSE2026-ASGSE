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
  loop invariant a >= b || b >= a;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x - (p * b + r * y);
  loop invariant a + b;
  loop invariant a != b ==> a > 0 && b > 0;
  loop invariant \exists integer k; k >= 0 && b == y - k * a;
  loop invariant \exists integer k; k >= 0 && a == x - k * b;
  loop invariant \exists integer k; k >= 0 && a == x - k * b && b == y - k * a;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (r - s) * y == (q - p) * x;
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
 
  //@ assert((r-s) * y == (q-p) * x);
}