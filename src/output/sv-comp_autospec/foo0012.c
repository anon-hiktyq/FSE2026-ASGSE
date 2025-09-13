



void foo0012(int n, int l) 
{
  int k = 1;

  
  
            
            /*@
          loop invariant (!(1 < \at(n,Pre))) ==> ((k == 1)&&(l == \at(l,Pre))&&(n == \at(n,Pre)));
            */
            for (; k < n; k++){

    int i= l;
    
    
            
            /*@
          loop invariant i >= l;
            */
            for (; i < n; i++){
      /*@ assert 1 <= i;*/
    }
            
    if(unknown1()) {
      l = l + 1;
    }
  }
            
}