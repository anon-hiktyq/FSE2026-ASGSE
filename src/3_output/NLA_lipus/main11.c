
/*@
    requires z>=0 && z<=10 && k>0 && k<=10;
    */
    
int main11(int z,int k,int a){
  

    int x=a;
    int y=1;
    int c=1;
  
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (1 < \at(k,Pre)) ==> (z*x - x + a - a*z*y == 0);
          loop invariant (1 < \at(k,Pre)) ==> (c >= 1 && c <= k);
          loop invariant (!(1 < \at(k,Pre))) ==> ((c == 1)&&(y == 1)&&(x == \at(a,Pre))&&(a == \at(a,Pre))&&(k == \at(k,Pre))&&(z == \at(z,Pre)));
          loop invariant a == \at(a,Pre);
          loop invariant k == \at(k,Pre);
          loop invariant z == \at(z,Pre);
          loop assigns c, x, y;
            */
            while (c < k){
   c = c + 1;
   x = x*z + a;
   y = y*z;
    }
            
  
  /*@ assert z*x-x+a-a*z*y == 0; */
  }
