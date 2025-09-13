
/*@ requires x >= 1;
    requires y >= 1;
*/
int main7(int x,int y){
  
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
  loop invariant \exists integer k; a == x*p + y*r + k*(x*q + y*s) && b == x*q + y*s + k*(x*p + y*r);
  loop invariant a == x*p + y*r;
  loop invariant b == x*q + y*s;
  loop assigns a;
  loop assigns b;
  loop assigns p;
  loop assigns q;
  loop assigns r;
  loop assigns s;
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

  //@ assert(b == x*q + y*s);
}