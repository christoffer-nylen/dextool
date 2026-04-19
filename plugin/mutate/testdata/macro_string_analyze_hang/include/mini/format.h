#pragma once
#include "mini/core.h"

namespace mini {

inline int use_string(basic_string_view<char>) { return 1; }

inline int heavy_branch(int x) {
  int sum = 0;
  if (x > 0 && x < 10) sum += 1;
  if (x > 1 && x < 11) sum += 2;
  if (x > 2 && x < 12) sum += 3;
  if (x > 3 && x < 13) sum += 4;
  if (x > 4 && x < 14) sum += 5;
  if (x > 5 && x < 15) sum += 6;
  if (x > 6 && x < 16) sum += 7;
  if (x > 7 && x < 17) sum += 8;
  return sum;
}

inline int run_format(int x) {
  int out = use_string(MINI_STRING("{}{}"));
  out += heavy_branch(x);
  out += heavy_branch(x + 1);
  out += heavy_branch(x + 2);
  return out;
}

}  // namespace mini
