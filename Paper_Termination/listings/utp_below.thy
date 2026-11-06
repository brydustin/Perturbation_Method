definition below :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat set" where
  "below R k = {q. q < k \<and> R q}"

definition max_below :: "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "max_below a f R k = Max (insert a (f ` below R k))"

definition min_below :: "real \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> real" where
  "min_below a f R k = Min (insert a (f ` below R k))"

definition agrees :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "agrees P f k \<longleftrightarrow> (\<forall>q<k. P q = f q)"
