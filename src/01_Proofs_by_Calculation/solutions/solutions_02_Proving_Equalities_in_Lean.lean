/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic

example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) :
  r = -7 :=
calc r = (r + 2 * s) - 2 * s : by ring
... = -1 - 2 * 3 : by rwa [h2, h1]
... = - 7 : by ring

example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
  (2 * a * n + b * m) ^ 2 = 2 :=
calc (2 * a * n + b * m) ^ 2
    = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) : by ring
... = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) : by rwa [h1, h2]
... = 2 : by ring

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
  d * (a * f - b * e) = 0 :=
calc d * (a * f - b * e) = (a * d) * f - d * b * e : by ring
... = (b * c) * f - d * b * e : by rwa [h1]
... = b * (c * f) - d * b * e  : by ring
... = b * (d * e) - d * b * e : by rwa [h2]
... = 0 : by ring
