definition kw :: real where "kw = 20 * pi"

definition M :: nat where "M = 1000"

definition grid :: "nat \<Rightarrow> real" where "grid m = 2 * pi * real m / real M"

definition steer :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex" where
  "steer p \<phi> j = cis (kw * (fst (p j) * cos \<phi> + snd (p j) * sin \<phi>))"

definition patt :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> complex" where
  "patt p N c \<phi> = (\<Sum>j<N. steer p \<phi> j * c j)"

definition sq :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> real" where
  "sq p N c m = (cmod (patt p N c (grid m)))\<^sup>2"

definition c0 :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> complex" where
  "c0 p t j = cnj (steer p t j)"

definition corr :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex" where
  "corr p N s c j = c j - patt p N c (grid s) / of_nat N * cnj (steer p (grid s) j)"
