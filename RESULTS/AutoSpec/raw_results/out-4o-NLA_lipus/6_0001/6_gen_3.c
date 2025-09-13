/*@ requires x >= 1;
    requires y >= 1;
*/
void main6(int x,int y){
  
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
  loop invariant a != b ==> (p * b + q * a == x);
  loop invariant a != b ==> (r * b + s * a == y);
  loop invariant a == b || (a != b && (a > b || b > a));
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