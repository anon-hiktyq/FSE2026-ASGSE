



/*@

ensures num <= 0 ==> \result == 0;

*/

int func26(int num) 
{
    int i = 0;
    int sum = 0;

    
            
        /*@
        logic int sum_pre = \at(sum, Pre);
        loop invariant sum == sum_pre + (\at(num, Pre) - num);
        loop invariant num >= 0;
        loop assigns i, sum, num;
        */
            while(num > 0) {
        i = num % 10;
        sum += i;
        num /= 10;
    }
            
    return sum;
}
void goo26() {
    int t = func26(123);
    //@ assert t == 6;
}