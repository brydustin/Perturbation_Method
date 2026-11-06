definition SS :: "(nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "SS r p N t = (cmod (FF r p N t))\<^sup>2"
