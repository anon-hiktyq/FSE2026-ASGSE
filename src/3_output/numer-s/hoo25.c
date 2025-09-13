
/*@
    requires n > 0;
    */
    
int hoo25(int n,int a) { 
    
    int i = 0;
    int sn = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= \at(n,Pre));
          loop invariant (0 < \at(n,Pre)) ==> (sn == i * a);
          loop invariant (!(0 < \at(n,Pre))) ==> ((sn == 0)&&(i == 0)&&(a == \at(a,Pre))&&(n == \at(n,Pre)));
          loop invariant a == \at(a,Pre);
          loop invariant n == \at(n,Pre);
          loop assigns sn, i;
            */
            while(i < n) {
      sn = sn + a;
      i++;
    }
            
  
    /*@ assert sn == n*a || sn == 0; */
}
