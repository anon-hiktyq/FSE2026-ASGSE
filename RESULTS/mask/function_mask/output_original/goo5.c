
/*@
  requires \valid(arr + (0 .. 4));
  assigns \nothing;
*/
void goo5() {
  int arr[5] = {1, 2, 3, 4, 5};
  int sum = arraysearch5(arr, 3, 5);
/* MASK_ACSL_ASSERT_LINE */
}
