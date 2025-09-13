

/*@
requires l > 0;
requires n > l;
*/
void foo03(int n, int l) {
  int i,k;

  k = 1;
  for (k=1; k<n; k++){
  	i = l;
    /*@
    loop invariant l <= i <= n;
    loop invariant i == l || i > l;
    loop invariant \forall integer m; l <= m < i ==> (1 <= m);
    loop assigns i;
    */
    for (; i<n; i++) {
    }

    }
  
    // @ assert \forall integer i; (l <= i < n) ==> (1 <= i); 
  

}
