definition pw :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> real" where
  "pw p N c \<phi> = (cmod (patt p N c \<phi>))\<^sup>2"
