


void foo007(int n) 
{
    int k = 0;
    int i = 0;


    
            
            /*@
          loop invariant (0 < \at(n,Pre)) ==> (((i == 0)&&(k == 0)&&(n == \at(n,Pre))) || ((i == k) && (0 <= i <= n)));
          loop invariant (0 < \at(n,Pre)) ==> (i == k) ;
          loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= n) ;
          loop invariant (!(0 < \at(n,Pre))) ==> ((i == 0)&&(k == 0)&&(n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
            */
            while (i < n) {
        i++;
        k++;
    }
            
    int j = n;


    
            
            /*@
          loop invariant j == k;
          loop invariant 0 <= j <= n;
          loop invariant k >= 0;
            */
            while (j > 0) {
        j--;
        k--;
        /*@ assert k >= 0; */
    }
            


}