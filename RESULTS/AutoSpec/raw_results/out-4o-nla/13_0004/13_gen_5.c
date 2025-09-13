/*@
requires x>=1 && y>=1;
*/
int main13(int x,int y){
   
    int a=x;
    int b=y;
    int p=1;
    int q=0;

    // loop body
    /*@
    loop invariant a >= 0 && b >= 0;
    loop invariant p == 2^(initial_a - a + initial_b - b); // where initial_a and initial_b are the initial values of a and b
    loop invariant q + a * p + b * p == x * y;
    loop assigns a, b, p, q;
    */
    while(a!=0 && b!=0) {
     if (a % 2 ==0 && b % 2 ==0 ){
          a = a/2;
          b = b/2;
          p = 4*p;
     }
     else if (a % 2 ==1 && b % 2 ==0 ){
          a = a-1;
          q = q+b*p;
     }
     else if (a % 2 ==0 && b % 2 ==1 ){
          b = b-1;
          q = q+a*p;
     }
     else {
          a = a-1;
          b = b-1;
          q = q+(a+b+1)*p;
     }
    }
    // @ assert q == x*y;
}
