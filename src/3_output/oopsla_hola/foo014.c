
/*@
    requires m > 0;
    */
    
void foo014(int m) {
  int a = 0;
  
  int j = 1;
  
  /*@
    // No invalid comments should be present
    */
    
  /*@
    loop invariant (1 <= \at(m,Pre)) ==> (a >= -m && a <= m);
    loop invariant (1 <= \at(m,Pre)) ==> (j >= 1 && j <= m + 1);
    loop invariant (!(1 <= \at(m,Pre))) ==> ((j == 1)&&(a == 0)&&(m == \at(m,Pre)));
    loop invariant m == \at(m,Pre);
    loop assigns a;
    loop assigns j;
  */
  for(j = 1; j <= m ; j++){
    if(unknown()) 
       a++;
    else
       a--; 
  }
            
  /*@ assert a >= -m && a <= m;*/
}
