definition cdist :: "real \<Rightarrow> real \<Rightarrow> real" where
  "cdist a b = \<bar>(a - b) - 2 * pi * of_int (round ((a - b) / (2 * pi)))\<bar>"
