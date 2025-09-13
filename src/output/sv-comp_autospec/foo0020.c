
/*@
    requires 0 <= n && n < 2;
    requires 0 <= v;
    */
    
void foo0020(int n, int v) {
  int c1 = 4000;
  int c2 = 2000;
  int c3 = 10000;
  
  int i, k, j;

  k = 0;
  i = 0;

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= \at(n,Pre));
            loop invariant (0 < \at(n,Pre)) ==> (k == i * (v == 0 ? c1 : (v == 1 ? c2 : c3)));
            loop invariant (!(0 < \at(n,Pre))) ==> ((k == 0)&&(i == 0)&&(c3 == 10000)&&(c2 == 2000)&&(c1 == 4000)&&(v == \at(v,Pre))&&(n == \at(n,Pre)));
            loop invariant c3 == 10000;
            loop invariant c2 == 2000;
            loop invariant c1 == 4000;
            loop invariant v == \at(v,Pre);
            loop invariant n == \at(n,Pre);
            loop assigns i, k;
            */
            while (i < n) {
    i++;
    if (v == 0)
      k += c1;
    else if (v == 1)
      k += c2;
    else
      k += c3;
  }
            

  j = 0;

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (0 <= j <= n);
            loop invariant k == (v == 0 ? c1 : (v == 1 ? c2 : c3)) * i - j; // Corrected line
            loop invariant n == \at(n, Pre);
            loop assigns j, k;
            */
            while (j < n) {
    /*@ assert k > 0; */
    j++;
    k--;
  }
}
