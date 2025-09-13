
void foo30() {
    int x = 100;

    /*@
      loop invariant x >= 0 && x <= 100;
      loop invariant \exists integer k; x == 100 - k && k >= 0 && k <= 100;
      loop assigns x;
    */
    while (x > 0) {
        x = x - 1;
    }
}
