definition prev_idx :: "nat \<Rightarrow> nat" where "prev_idx m = (m + M - 1) mod M"
definition next_idx :: "nat \<Rightarrow> nat" where "next_idx m = (m + 1) mod M"

definition is_peak :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_peak p N c m \<longleftrightarrow> sq p N c m > sq p N c (prev_idx m) \<and> sq p N c m > sq p N c (next_idx m)"
