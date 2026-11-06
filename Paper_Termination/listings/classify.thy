definition PP where "PP p q N R Hb lo hi m \<longleftrightarrow> m < M \<and> 0 < upper (DP p q N R Hb lo hi m) \<and> 0 < upper (DN p q N R Hb lo hi m)"
definition CP where "CP p q N R Hb lo hi m \<longleftrightarrow> m < M \<and> 0 < lower (DP p q N R Hb lo hi m) \<and> 0 < lower (DN p q N R Hb lo hi m)"
definition PO where "PO p lo hi n0 band m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some D \<Rightarrow> lower D < DMAX p lo hi n0 m)"
definition CO where "CO p lo hi n0 band m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some D \<Rightarrow> upper D < DMIN p lo hi n0 m)"
definition PM where "PM p q N R Hb lo hi n0 m \<longleftrightarrow> PP p q N R Hb lo hi m \<and>
   (\<forall>k < M. CP p q N R Hb lo hi k \<longrightarrow> DMIN p lo hi n0 m \<le> DMAX p lo hi n0 k)"

definition run_ok where "run_ok p q N R Hb lo hi n0 RS \<longleftrightarrow>
   (\<forall>r \<in> RS. PP p q N R Hb lo hi r) \<and>
   (\<forall>r \<in> RS. \<forall>k < M. PP p q N R Hb lo hi k \<and> k \<notin> RS \<longrightarrow> DMAX p lo hi n0 r < DMIN p lo hi n0 k)"
definition EXC where "EXC p q N R Hb lo hi n0 m \<longleftrightarrow> m < M \<and>
   (run_ok p q N R Hb lo hi n0 {m} \<or> run_ok p q N R Hb lo hi n0 {m, next_idx m} \<or> run_ok p q N R Hb lo hi n0 {prev_idx m, m})"

definition GL where "GL p q N R Hb lo hi = Max ((LOB p q N R Hb lo hi) ` {..<M})"
definition US where "US p q N R Hb lo hi n0 band =
   Max (insert 0 ((UPB p q N R Hb lo hi) ` {m. PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m}))"

definition inv100_ivl :: "float interval" where
  "inv100_ivl = Ivl (Float 11529215046068469 (-60)) (Float 11529215046068470 (-60))"

lemma inv100_in: "1 / 100 \<in>\<^sub>r inv100_ivl"
  unfolding inv100_ivl_def by (intro in_real_intervalI) (simp_all add: Ivl_simps real_of_float_eq)

definition TH where "TH p q N R Hb lo hi = mult_float_interval p (interval_of (GL p q N R Hb lo hi)) inv100_ivl"

definition terminal where "terminal p q N R Hb lo hi n0 band \<longleftrightarrow> US p q N R Hb lo hi n0 band \<le> lower (TH p q N R Hb lo hi)"

definition LL where "LL p q N R Hb lo hi n0 band =
   Max (insert 0 ((LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and> \<not> PM p q N R Hb lo hi n0 k}))"

definition cand where "cand p q N R Hb lo hi n0 band m \<longleftrightarrow>
   PP p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXC p q N R Hb lo hi n0 m \<and>
   lower (TH p q N R Hb lo hi) \<le> UPB p q N R Hb lo hi m \<and>
   \<not> (0 < LL p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi m < LL p q N R Hb lo hi n0 band)"
