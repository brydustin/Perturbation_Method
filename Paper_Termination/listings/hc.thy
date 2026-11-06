definition Bc :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where "Bc r N = (\<Sum>j<N. cmod (r j))"
definition Dc :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Dc r p N = (\<Sum>j<N. cmod (r j) * gam p j)"
definition Ec :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Ec r p N = (\<Sum>j<N. cmod (r j) * (gam p j + (gam p j)\<^sup>2))"
definition Hc :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real" where
  "Hc r p N = 2 * ((Dc r p N)\<^sup>2 + Bc r N * Ec r p N)"
