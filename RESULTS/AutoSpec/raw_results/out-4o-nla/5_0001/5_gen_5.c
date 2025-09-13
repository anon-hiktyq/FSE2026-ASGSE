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
  loop invariant a >= 1;
  loop invariant b >= 1;
  loop invariant a == x - b*p + y*q;
  loop invariant b == y - x*r + a*s;
  loop invariant x*r + b*s == y;
  loop invariant x*p + b*q == x;
  loop invariant 1 == p*s - r*q;
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
