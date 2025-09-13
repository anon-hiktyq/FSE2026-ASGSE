
int unknown1();
int unknown2();
int unknown3();



void foo09(int pvlen) {
  
  int t;
  int k = 0;
  int n;
  int i = 0;

 
  /*@
  loop invariant \forall integer j; 0 <= j < i ==> j <= pvlen;
  loop invariant \forall integer j; 0 <= j < i ==> i <= pvlen;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  loop assigns pvlen;
  loop assigns i;
  */
  while (unknown1()){
    i = i + 1;
  
  if (i > pvlen) {
    pvlen = i;
  } else {

  }
}
  i = 0;

 
  /*@
  loop invariant k == i;
  loop invariant i == k;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  loop assigns t;
  loop assigns k;
  loop assigns i;
  */
  while (unknown2()) {
    t = i;
    i = i + 1;
    k = k + 1;
  }
  /*@
  loop invariant k == i;
  loop invariant i == k;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  loop assigns \nothing;
  */
  while (unknown3()){
      ;
  }

  int j = 0;
  n = i;
  
  /*@
  loop invariant n == i + j;
  loop invariant k == n - j;
  loop invariant k == i;
  loop invariant k <= n;
  loop invariant j <= n;
  loop invariant j + i == n;
  loop invariant i == n - j;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant i + j == n;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns j;
  loop assigns i;
  */
  while (1) {
    
    k = k - 1;
    i = i - 1;
    j = j + 1;
    if (j < n) {
    } else {
      break;
    }
    //@ assert k >= 0;
  }
}
