
/*@
requires sum != 0;;
requires sum != 0;
requires a >= 0;
requires a == 0 || a != 0;;
requires a == 0 || a != 0;
requires a != 0 ==> sum == 10;
ensures sum != 0 ==> \result == 10 / sum;
ensures a == 0 ==> \result == 0; // If a is 0, x and y are both 0, leading to division by zero;
ensures a == 0 ==> \result == 0;
ensures a != 0 ==> \result == 2;
ensures \result == 2; // If a is non-zero, sum is 10, hence 10/10 = 1;
ensures \result == 0 ==> a == 0;
ensures \result == (a == 0 ? 0 : 2);
ensures \result == (a == 0 ? 0 : 10 / (5 + 5));
ensures \result == (10 / sum);
ensures \result == (10 / (x + y));
ensures \result == (10 / (5 + 5)) ==> a != 0;
assigns x, y, sum, res;
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