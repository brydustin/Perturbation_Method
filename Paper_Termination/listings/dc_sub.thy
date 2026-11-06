definition dc_sub :: "float interval option \<Rightarrow> nat \<Rightarrow> bool" where
  "dc_sub band j = check_sector 53 dc_q 9 inv9_ivl band 20 (Float 1 (-26)) 100 (Float (int j) (-12)) (Float (int j + 1) (-12))"
