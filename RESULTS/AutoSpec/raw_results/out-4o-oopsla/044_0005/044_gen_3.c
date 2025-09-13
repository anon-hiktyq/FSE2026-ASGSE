

void foo044(int k, int flag , int __BLAST_NONDET) {
  int i=0;
  int j=0;
  int n;
 

  if (flag == 1){
     n=1;
  } else {
     n=2;
  }

  i=0;
  
  /*@
  loop invariant 0 <= i <= k + 1;
  loop invariant j == i * n;
  loop invariant flag == 1 ==> j == i;
  loop invariant flag != 1 ==> j == 2 * i;
  loop assigns i;
  loop assigns j;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
  // @ assert (flag == 1) ==> (j == i);*/
    
	
}
