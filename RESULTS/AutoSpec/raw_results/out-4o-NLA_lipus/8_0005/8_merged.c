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
  loop invariant y == a * r + b * s;
  loop invariant x > 0 && y > 0;
  loop invariant x == a * p + b * q;
  loop invariant p == r + 1;
  loop invariant a >= b || b >= a;
  loop invariant a >= 1 || b >= 1;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == b ==> (r - s) * y == (q - p) * x;
  loop invariant a + b == x + y;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 <= s;
  loop invariant 0 <= q;
  loop invariant 0 <= p;
  loop invariant 0 < b;
  loop invariant 0 < a;
  loop invariant (r-s) * a + (q-p) * b == (r-s) * x + (q-p) * y;
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