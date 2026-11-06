primrec rows :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "rows p N [] m j = steer p (grid m) j"
| "rows p N (s # \<sigma>) m j = rows p N \<sigma> m j - gram p N m s * rows p N \<sigma> s j"

primrec exc :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> complex" where
  "exc p N c [] = c"
| "exc p N c (s # \<sigma>) = corr p N s (exc p N c \<sigma>)"
