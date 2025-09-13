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
  loop invariant x > 0 && y > 0;
  loop invariant a == x - (p-q) * b;
  loop invariant b == y - (r-s) * a;
  loop invariant a == x - (p-q) * b;
  loop invariant a == x - (p-q) * b;
  loop invariant \forall integer k; 0 <= k <= x <==> a >= 1;
  loop invariant \forall integer k; 0 <= k <= y <==> b >= 1;
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