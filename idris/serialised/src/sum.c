#include <stdio.h>

int sumAt (int buf[], int *ptr, int *res) {
  // read the tag, move the pointer past it
  int tag = buf[*ptr]; (*ptr)++;
  switch (tag) {
    case 0: // a leaf
      printf("leaf");
      return 0;
    case 1: // a node
      printf("(node ");
      int lsum = sumAt(buf, ptr, res); // sum the left subtree
      // read the stored value, move the pointer past it
      int val  = buf[*ptr]; (*ptr)++;
      *res += val; // add the value to the accumulator
      printf(" %d ", val);
      int rsum = sumAt(buf, ptr, res);  // sum the right subtree
      printf(")");
      return 0;
    default: return -1;
}}

int main () {
  int buf[] = {1, 0, 10, 1, 1, 0, 100, 1, 0, 1, 0, 20, 0};
  int ptr = 0;
  int sum = 0;
  int res = sumAt(buf,&ptr,&sum);
  if (res < 0) { return res; }
  else {
    printf("\nSum: %d\n",sum);
    return 0;
}}
