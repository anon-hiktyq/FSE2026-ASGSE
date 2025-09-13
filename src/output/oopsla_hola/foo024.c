
void foo024(int n) {
  int i,j,k;
  
  i=0;
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant (0<\at(n,Pre)) ==> (0 <= i < n);
              loop invariant (!(0<\at(n,Pre))) ==> ((i == 0)&&(n == \at(n,Pre)));
              loop invariant n == \at(n,Pre);
              loop assigns \nothing;
            */
            for (i=0;i<n;i++){

    j=i;
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              // Loop invariant: At the start of each iteration of the loop over j,
              // we have that j >= i and j < n.
              loop invariant i <= j < n;
              loop assigns \nothing;
            */
            for (j=i;j<n;j++){

      k=j;
      
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              // Loop invariant: At the start of each iteration of the loop over k,
              // we have that k >= j and k < n.
              loop assigns \nothing;
            */
            for (k=j;k<n;k++){
	       /*@assert k >= i;*/
      }
            
    }
            
  }
}
