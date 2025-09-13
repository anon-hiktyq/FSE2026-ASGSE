
/*@
  predicate sum_sequence(integer k) = 
    \forall integer i; 0 <= i <= k ==> \exists integer s; s == i * (i + 1) / 2;

*/

/*@
    requires k >= 0 && k <= 30;
*/
int main15(int k){
   
    int y=0;
    int x=0;
    int c=0;
  

    // loop body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(k,Pre)) ==> (y == c);
          loop invariant (0 < \at(k,Pre)) ==> (x == (c * (c + 1)) / 2);
          loop invariant (0 < \at(k,Pre)) ==> (0 <= c <= k);
          loop invariant (!(0 < \at(k,Pre))) ==> ((c == 0)&&(x == 0)&&(y == 0)&&(k == \at(k,Pre)));
          loop invariant k == \at(k,Pre);
          loop assigns c, y, x;
            */
            while(c < k){
     c = c + 1;
     y = y + 1;
     x = y + x;
    }
            

    /*@ assert 2 * x - k * k - k == 0; */
}
