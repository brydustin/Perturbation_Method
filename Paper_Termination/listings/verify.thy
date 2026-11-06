fun verify :: "nat \<Rightarrow> (nat \<Rightarrow> float \<times> float) \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow>
               float interval option \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> nat \<Rightarrow> float \<Rightarrow> float \<Rightarrow> nat list \<Rightarrow> bool" where
  "verify p q N IN n0f band Dmax wmin 0 lo hi \<sigma> = False"
| "verify p q N IN n0f band Dmax wmin (Suc f) lo hi \<sigma> =
     (let R = Rref p q N IN \<sigma>; Hb = Hbref p q N IN \<sigma>; n0 = n0f lo hi in
      if \<not> all_ok p lo hi n0 then False
      else if terminal p q N R Hb lo hi n0 band then True
      else let K = cands p q N R Hb lo hi n0 band in
        if (length K \<noteq> 1 \<or> Dmax \<le> length \<sigma>) \<and> wmin < hi - lo
          then verify p q N IN n0f band Dmax wmin f lo (tc lo hi) \<sigma> \<and> verify p q N IN n0f band Dmax wmin f (tc lo hi) hi \<sigma>
        else if K = [] then True
        else if Dmax \<le> length \<sigma> then False
        else list_all (\<lambda>s. verify p q N IN n0f band Dmax wmin f lo hi (s # \<sigma>)) K)"
