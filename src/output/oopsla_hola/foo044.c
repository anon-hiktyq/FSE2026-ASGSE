
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
    loop invariant (0 <= \at(k,Pre)) ==> (0 <= i <= k + 1);
    loop invariant (0 <= \at(k,Pre)) ==> (j == i * n);
    loop invariant (!(0 <= \at(k,Pre))) ==> ((j == 0) && (i == 0) && (__BLAST_NONDET == \at(__BLAST_NONDET,Pre)) && (flag == \at(flag,Pre)) && (k == \at(k,Pre)));
    loop invariant (flag == 1) ==> (n == 1);
    loop invariant (flag != 1) ==> (n == 2);
    loop invariant __BLAST_NONDET == \at(__BLAST_NONDET,Pre);
    loop invariant flag == \at(flag,Pre);
    loop invariant k == \at(k,Pre);
    loop assigns i, j;
  */
  while ( i <= k) {
    i++;
    j = j + n;
  }
            
  /*@ assert (flag == 1) ==> (j == i);*/
}
