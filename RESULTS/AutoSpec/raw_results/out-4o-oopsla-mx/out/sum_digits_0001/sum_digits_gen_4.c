int func(int num) {
    int i = 0;
    int sum = 0;

    /*@
    loop invariant num >= 0;
    loop invariant sum >= 0;
    loop invariant \forall integer k; 0 <= k <= sum ==> sum == (sum + num); 
    loop assigns i;
    loop assigns sum;
    loop assigns num;
    */
    while(num>0) {
        i = num%10;
        sum += i;
        num /= 10;
    }
    return sum;
}

// write a test
void main() {
    int t = func(123);
    // @ assert t == 6;
}