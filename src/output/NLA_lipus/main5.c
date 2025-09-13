
/*@
    requires x >= 1;
    requires y >= 1;
    */
    
int main5(int x,int y){
  
  int a,b,p,q,r,s;
  // Removed the redefinition of 'x' and 'y'
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant 1 == p * s - r * q;
            loop invariant a >= 0;
            loop invariant b >= 0;
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
            
 
  /*@ assert(1 == p*s - r*q); */
}
