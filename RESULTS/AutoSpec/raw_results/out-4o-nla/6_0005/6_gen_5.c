/*@ requires x >= 1;
    requires y >= 1;
*/
int main6(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant a >= 1 && b >= 1;
  loop invariant x == a*p + b*q;
  loop invariant y == a*r + b*s;
  loop invariant a >= 1 && b >= 1;
  loop invariant x*r - y*p == a;
  loop invariant (a == x && b == y) || (a == b);
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
 
  //@ assert(a == y*r + x*p);
 
}