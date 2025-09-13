
/*@
    requires n > 0;
    requires n < 10;
    */
    
void foo021(int n,int j,int v) {
  int c1 = 4000;
  int c2 = 2000;
  int i = 0;
  int k = 0;
 
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (((k == 0)&&(i == 0)&&(c2 == 2000)&&(c1 == 4000)&&(v == \at(v,Pre))&&(j == \at(j,Pre))&&(n == \at(n,Pre))) || (v == 0 ==> k == 4000 * i + 2000 * (\at(n,Pre) - i)) || (v == 1 ==> k == 2000 * i + 4000 * (\at(n,Pre) - i)));
          loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= n);
          loop invariant (0 < \at(n,Pre)) ==> (k >= 2000 * i);
          loop invariant (0 < \at(n,Pre)) ==> (k <= 4000 * i);
          loop invariant (!(0 < \at(n,Pre))) ==> ((k == 0)&&(i == 0)&&(c2 == 2000)&&(c1 == 4000)&&(v == \at(v,Pre))&&(j == \at(j,Pre))&&(n == \at(n,Pre)));
          loop invariant c2 == 2000;
          loop invariant c1 == 4000;
          loop invariant j == \at(j,Pre);
          loop invariant n == \at(n,Pre);
          loop assigns i, k, v;
            */
            while( i < n ) {
    i++;
    if(unknown() % 2 == 0) {
        v = 0;
    }
    else v = 1;
    
    if( v == 0 ){
      k += c1;
    }else {
      k += c2;
    }
  }
            
  
  /*@ assert k > n; */
}
