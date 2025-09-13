
/*@
    requires z>=0 && z<=10 && k>0 && k<=10;
    */
    
int main9(int z,int k){
  

  int x=1;
  int y=z;
  int c=1;

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (1 < \at(k,Pre)) ==> (x*z - x - y + 1 == 0);
          loop invariant (1 < \at(k,Pre)) ==> (c >= 1);
          loop invariant (1 < \at(k,Pre)) ==> (c <= k);
          loop invariant (!(1 < \at(k,Pre))) ==> ((c == 1)&&(y == \at(z,Pre))&&(x == 1)&&(k == \at(k,Pre))&&(z == \at(z,Pre)));
          loop invariant k == \at(k,Pre);
          loop invariant z == \at(z,Pre);
          loop assigns c, x, y;
            */
            while (c < k){
 c = c + 1;
 x = x*z + 1;
 y = y*z;
  }
            

/*@ assert x*z - x - y + 1 == 0; */
}
