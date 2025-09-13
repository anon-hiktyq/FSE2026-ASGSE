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
  loop invariant x*r + y*s == b;
  loop invariant x*p + y*q == a;
  loop invariant x * s - y * p == b;
  loop invariant x * r - y * q == a;
  loop invariant p*s - q*r == 1;
  loop invariant b == y*s + x*q;
  loop invariant b == y * s + x * q;
  loop invariant b == x*r + y*s;
  loop invariant b == x*q + y*s;
  loop invariant b == gcd(x, y);
  loop invariant a >= 1 || b >= 1;
  loop invariant a >= 1 && b >= 1;
  loop invariant a >= 0 && b >= 0;
  loop invariant a == y*r + x*p;
  loop invariant a == y * r + x * p;
  loop invariant a == x*p + y*r;
  loop invariant a == x*p + y*q;
  loop invariant a == gcd(x, y);
  loop invariant a == b + (x*(p-q) + y*(r-s));
  loop invariant a != b ==> \exists integer k; k >= 0 && a == b + k*(x*p + y*r);
  loop invariant \exists integer k; x*p + y*q == x && x*r + y*s == y;
  loop invariant \exists integer k; a == b == k;
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
 
  //@ assert(a == y*r + x*p);
 
}