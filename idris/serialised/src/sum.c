#include <stdio.h>
#include <stdlib.h>

int sumAt (int buf[], int *ptr, int *res, char *str) {
  // read the tag, move the pointer past it
  int tag = buf[*ptr]; (*ptr)++;
  switch (tag) {
    case 0: // a leaf
      sprintf(str, "%sleaf", str);
      return 0;
    case 1: // a node
      sprintf(str, "%s(node ", str);
      sumAt(buf, ptr, res, str) < 0; // sum the left subtree
      // read the stored value, move the pointer past it
      int val  = buf[*ptr]; (*ptr)++;
      *res += val; // add the value to the accumulator
      sprintf(str, "%s %d ", str, val);
      sumAt(buf, ptr, res, str) < 0; // sum the right subtree
      sprintf(str, "%s)", str);
      return 0;
    default:
      printf("Invalid format\n");
      exit(-1);
}}

int main () {
  int buf[] = {1, 0, 10, 1, 1, 0, 100, 1, 0, 1, 2, 20, 0};
  int ptr = 0;
  int sum = 0;
  char str[10000];
  sumAt(buf, &ptr, &sum, str);
  printf("%s\nSum: %d\n", str, sum);
  return 0;
}
