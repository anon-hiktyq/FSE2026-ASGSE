
/*@

ensures 7 > n ==> \result == 1;

*/

int fun17(int n) 
{
    int i = 7;
    int x = 1;

    /*@
      loop invariant (7 <= \at(n,Pre)) ==> (x == 1 + ((i - 7) / 3)) ;
      loop invariant (7 <= \at(n,Pre)) ==> (7 <= i <= n + 3) ;
      loop invariant (!(7 <= \at(n,Pre))) ==> ((x == 1)&&(i == 7)&&(n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop invariant i <= n ==> (x == 1 + ((i - 7) / 3)) ;
      loop invariant i > n ==> (x == 1 + ((n - 7) / 3) + 1) ;
      loop variant n - i;
    */
    while(i <= n) {
        x += 1;
        i += 3;
    }
            
    return x;
}

/*@
    ensures \result == 3; 
*/

int main17() {
    int a = fun17(10);
    //@ assert a == 3;
}
