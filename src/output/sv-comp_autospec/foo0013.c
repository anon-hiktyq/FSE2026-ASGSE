


void foo0013(int n, int m , int l) 
{
    int i, j, k;

    i = 0;
    
            
            /*@
          loop invariant (!(0 < \at(n,Pre))) ==> ((i == 0)&&(l == \at(l,Pre))&&(m == \at(m,Pre))&&(n == \at(n,Pre)));
            */
            for (i = 0; i < n; i++) {
        j = 2 * i;
        
            
            /*@
            */
            for (j = 2 * i; j < 3 * i; j++) {
            k = i;
            
            
            
            /*@
            loop invariant i <= k <= j;
            */
            for (k = i; k < j; k++) {
                /*@ assert k - i <= 2 * n; */
            }
            
        }
            
    }
            
}