definition certificate :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "certificate \<Delta> \<psi> \<mu> \<Lambda> e \<longleftrightarrow> (\<Sum>q\<in>Qset \<Delta>. cmod (\<mu> q)) \<le> \<Lambda> \<and>
     (\<Sum>j<32. (cmod (steer ucp (grid \<psi>) j - (\<Sum>q\<in>Qset \<Delta>. \<mu> q * steer ucp (grid q) j)))\<^sup>2) \<le> e\<^sup>2"
