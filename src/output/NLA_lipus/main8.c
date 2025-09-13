
/*@
    requires x >= 1;
    requires y >= 1;
    */
    
int main8(int x,int y){
  
  int a,b,p,q,r,s;
 
  a = x;
  b = y;
  p = 1;
  q = 0;
  r = 0;
  s = 1;

 
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant a >= 0 && b >= 0;
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
            
 
  /*@ assert((r-s) * y == (q-p) * x); */
}
