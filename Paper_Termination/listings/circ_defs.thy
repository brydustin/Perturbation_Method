definition rc :: real where "rc = 2 / 5"
definition theta :: "nat \<Rightarrow> real" where "theta j = 2 * pi * real j / 32"
definition ucp :: "nat \<Rightarrow> real \<times> real" where "ucp j = (rc * cos (theta j), rc * sin (theta j))"

abbreviation Fc :: "(nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> complex" where "Fc c m \<equiv> patt ucp 32 c (grid m)"

definition Qset :: "nat \<Rightarrow> nat set" where "Qset \<Delta> = {m. m < M \<and> 100 * \<Delta> < 36 * min m (M - m)}"
