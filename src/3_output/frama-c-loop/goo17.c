


int fun17(int n) {
    int i = 7;
    int x = 1;

    /*@
      loop invariant (7 <= \at(n,Pre)) ==> (i == 7 + 3 * (x - 1)); 
      loop invariant (7 <= \at(n,Pre)) ==> (x == 1 + (i - 7) / 3 + ((i - 7) % 3 == 0 ? 0 : 1)); 
      loop invariant (!(7 <= \at(n,Pre))) ==> ((x == 1) && (i == 7) && (n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop assigns i, x;
      loop variant n - i;
    */
    while(i <= n) {
        x += 1;
        i += 3;
    }
    
    /*@ assert (7 <= \at(n,Pre)) ==> (x == 1 + (n - 7) / 3 + 1); */
    /*@ assert (!(7 <= \at(n,Pre))) ==> (x == 1); */
    return x;
}

int goo17() {
    int a = fun17(10);
    //@ assert a == 3;
}