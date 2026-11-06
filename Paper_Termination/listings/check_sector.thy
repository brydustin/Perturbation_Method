definition check_sector :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> bool" where
  "check_sector p q N IN band Dmax wmin f lo hi =
     (let kl = kernelL p q N; gl = gridLst p in
      verify_impl p q N IN kl gl band Dmax wmin f lo hi [] kl (hbL p q N kl))"
