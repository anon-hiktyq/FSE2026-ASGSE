



void foo031(int i,int j,int k,int n,int m) 
{

  i = 0;
  
            
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (j >= i && j < m);
          loop invariant (0 < \at(n,Pre)) ==> (k >= 0 && k < j);
            */
            
            
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (((m == \at(m,Pre)) && (n == \at(n,Pre)) && (k == \at(k,Pre)) && (j == \at(j,Pre)) && (i == 0)) || (j < m));
          loop invariant (0 < \at(n,Pre)) ==> (i >= 0 && i < n);
          loop invariant (0 < \at(n,Pre)) ==> (((m == \at(m,Pre)) && (n == \at(n,Pre)) && (k == \at(k,Pre)) && (j == \at(j,Pre)) && (i == 0)) || (j >= i && j < m));
          loop invariant (0 < \at(n,Pre)) ==> (((m == \at(m,Pre)) && (n == \at(n,Pre)) && (k == \at(k,Pre)) && (j == \at(j,Pre)) && (i == 0)) || (k >= 0 && k < j));
          loop invariant (!(0 < \at(n,Pre))) ==> ((m == \at(m,Pre)) && (n == \at(n,Pre)) && (k == \at(k,Pre)) && (j == \at(j,Pre)) && (i == 0));
          loop invariant m == \at(m,Pre);
          loop invariant n == \at(n,Pre);
            */
            for (i = 0; i < n; i += 4) {
    j = i;
    
            
        /*@ loop invariant j >= i && j < m; */
        
            /*@
          loop invariant k >= 0 && k < j; 
            */
            for (j = i; j < m;) {
        
      if (unknown()) {
        /*@ assert j >= 0;*/
        j++;
        k = 0;
        
        /*@ loop invariant j >= i && j < m; */
        
            /*@
            */
            while (k < j) {
          k++;
        }
            
      } else {
        /*@ assert n + j + 5 > i;*/
        j += 2;
      }
    }
            
  }
}