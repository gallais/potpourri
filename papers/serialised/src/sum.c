#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int sumAt (uint8_t buf[], int *ptr, char *str) {
  // read the tag, move the pointer past it
  uint8_t tag = buf[*ptr]; (*ptr)++;
  switch (tag) {
    case 0: // a leaf
      sprintf(str, "%sleaf", str);
      return 0;
    case 1: // a node
      sprintf(str, "%s(node ", str);
      int m = sumAt(buf, ptr, str); // sum the left subtree
      // read the stored value, move the pointer past it
      uint8_t val = buf[*ptr]; (*ptr)++;
      sprintf(str, "%s %d ", str, val);
      int n = sumAt(buf, ptr, str); // sum the right subtree
      sprintf(str, "%s)", str);
      return (m + (int) val + n);
    default:
      printf("Invalid format: %d\n", tag);
      exit(-1);
}}

int main () {
  // uint8_t buf[] = {1, 1, 0, 4, 1, 0, 0, 0, 10, 1, 1, 0, 100, 1, 0, 1, 0, 20, 0};
  uint8_t buf[] = {01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x05, 0x00, 0x0a, 0x01, 0x00, 0x14, 0x00};
  int ptr = 0;
  char str[10000];
  int sum = sumAt(buf, &ptr, str);
  printf("%s\nSum: %d\n", str, sum);
  return 0;
}
