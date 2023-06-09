#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

void sumAt (uint8_t buf[], int *ptr, int *res, char *str) {
  // read the tag, move the pointer past it
  uint8_t tag = buf[*ptr]; (*ptr)++;
  switch (tag) {
    case 0: // a leaf
      sprintf(str, "%sleaf", str);
      return;
    case 1: // a node
      sprintf(str, "%s(node ", str);
      sumAt(buf, ptr, res, str); // sum the left subtree
      // read the stored value, move the pointer past it
      uint8_t val = buf[*ptr]; (*ptr)++;
      *res += (int) val; // add the value to the accumulator
      sprintf(str, "%s %d ", str, val);
      sumAt(buf, ptr, res, str); // sum the right subtree
      sprintf(str, "%s)", str);
      return;
    default:
      printf("Invalid format: %d\n", tag);
      exit(-1);
}}

int main () {
  // uint8_t buf[] = {1, 1, 0, 4, 1, 0, 0, 0, 10, 1, 1, 0, 100, 1, 0, 1, 0, 20, 0};
  uint8_t buf[] = {01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x05, 0x00, 0x0a, 0x01, 0x00, 0x14, 0x00};
  int ptr = 0;
  int sum = 0;
  char str[10000];
  sumAt(buf, &ptr, &sum, str);
  printf("%s\nSum: %d\n", str, sum);
  return 0;
}
