/*@ requires x >= 1;
    requires y >= 1;
*/
void main5(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  /*@
  loop invariant y == a*r + b*s;
  loop invariant x == a*p + b*q;
  loop invariant p*s - r*q == 1;
  loop invariant b == y - k * a;
  loop invariant b == x*q + y*s;
  loop invariant b == x * q + y * s;
  loop invariant a >= 1 && b >= 1;
  loop invariant a == x*p + y*r;
  loop invariant a == x - k * b;
  loop invariant a == x - k * b || b == y - k * a;
  loop invariant a == x * p + y * r;
  loop invariant a == 0 || b == 0 || gcd(a, b) == gcd(x, y);
  loop invariant a <= x && b <= y;
  loop invariant \exists integer k; k > 0 && a == k * b || b == k * a;
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
