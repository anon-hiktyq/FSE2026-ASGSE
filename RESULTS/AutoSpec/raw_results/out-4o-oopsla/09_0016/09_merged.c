
int unknown1();
int unknown2();
int unknown3();



void foo09(int pvlen) {
  
  int t;
  int k = 0;
  int n;
  int i = 0;

 
  /*@
  loop invariant k == 0;
  loop invariant \forall integer m; 0 <= m < i ==> m <= pvlen;
  loop invariant \forall integer m; 0 <= m < i ==> m < pvlen + 1;
  loop invariant \forall integer j; 0 <= j < i ==> j <= pvlen;
  loop invariant 0 <= k;
  loop invariant 0 <= i;
  loop assigns t;
  loop assigns pvlen;
  loop assigns k;
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
  loop invariant i - k == 0;
  loop invariant \forall integer m; 0 <= m < i ==> m >= 0;
  loop invariant \forall integer m; 0 <= m < i ==> m < i + 1;
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
  loop invariant i - k == 0;
  loop invariant \true;
  loop invariant \forall integer m; 0 <= m < i ==> m >= 0;
  loop invariant \forall integer m; 0 <= m < i ==> m < i + 1;
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
  loop invariant k == n - j;
  loop invariant k == i;
  loop invariant k <= n;
  loop invariant j <= n;
  loop invariant j + i == n;
  loop invariant i == n - j;
  loop invariant i == k;
  loop invariant i <= n;
  loop invariant i + j == n;
  loop invariant \forall integer m; 0 <= m < j ==> m >= 0;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant -1 <= k;
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
