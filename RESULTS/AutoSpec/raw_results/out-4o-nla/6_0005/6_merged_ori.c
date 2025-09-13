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
  loop invariant y == a*r + b*s;
  loop invariant x*r - y*p == a;
  loop invariant x*q + y*s == b;
  loop invariant x*p + y*r == a;
  loop invariant x == a*p + b*q;
  loop invariant s*x - r*y == 0;
  loop invariant p*y - q*x == 0;
  loop invariant b == y*s + x*q;
  loop invariant b == x*q + y*s;
  loop invariant b == \old(b) - (a * (s - \old(s))) + (x * (q - \old(q)));
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == y*r + x*p;
  loop invariant a == x*p + y*r;
  loop invariant a == \old(a) - (b * (r - \old(r))) + (y * (s - \old(s)));
  loop invariant a != b ==> (\exists integer k; k >= 0 && (a == x*p + y*r - k*b || b == x*q + y*s - k*a));
  loop invariant \exists integer k; a == b + k * (y - x);
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant (x == a*p + b*q) && (y == a*r + b*s);
  loop invariant (a == x && b == y) || (a == b);
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
 
  //@ assert(a == y*r + x*p);
 
}