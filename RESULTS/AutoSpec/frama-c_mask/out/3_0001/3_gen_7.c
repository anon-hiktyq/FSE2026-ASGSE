
/*@
requires a >= 0;
ensures \result == 2;  // If a is non-zero, sum is 10, hence 10/10 = 1
ensures a == 0 ==> \result == 0;  // If a is 0, x and y are both 0, leading to division by zero
assigns \nothing;
*/
int func(int a) {
    int x, y;
    int sum, res;
    if (a == 0){
        x = 0; y = 0;
    }
    else {
        x = 5; y = 5;
    }
    sum = x + y; 
    res = 10/sum; 
    return res;
}

int main() {
    int a = func(4);
    return 0;
}