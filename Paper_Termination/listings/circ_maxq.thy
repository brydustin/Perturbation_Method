definition maxQ :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real" where
  "maxQ \<Delta> c = Max ((\<lambda>q. cmod (Fc c q)) ` Qset \<Delta>)"
definition maxAll :: "(nat \<Rightarrow> complex) \<Rightarrow> real" where
  "maxAll c = Max ((\<lambda>m. cmod (Fc c m)) ` {..<M})"
definition l2 :: "(nat \<Rightarrow> complex) \<Rightarrow> real" where
  "l2 c = L2_set (\<lambda>j. cmod (c j)) {..<32}"
