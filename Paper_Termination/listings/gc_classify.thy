definition PPg where "PPg p q N R Hb lo hi m \<longleftrightarrow> m < M \<and> 0 \<le> upper (DP p q N R Hb lo hi m) \<and> 0 \<le> upper (DN p q N R Hb lo hi m)"
definition PMg where "PMg p q N R Hb lo hi n0 m \<longleftrightarrow> PPg p q N R Hb lo hi m \<and>
   (\<forall>k < M. CP p q N R Hb lo hi k \<longrightarrow> DMIN p lo hi n0 m \<le> DMAX p lo hi n0 k)"

definition run_okg where "run_okg p q N R Hb lo hi n0 RS \<longleftrightarrow>
   (\<forall>r \<in> RS. PPg p q N R Hb lo hi r) \<and>
   (\<forall>r \<in> RS. \<forall>k < M. PPg p q N R Hb lo hi k \<and> k \<notin> RS \<longrightarrow> DMAX p lo hi n0 r < DMIN p lo hi n0 k)"
definition EXCg where "EXCg p q N R Hb lo hi n0 m \<longleftrightarrow> m < M \<and>
   (run_okg p q N R Hb lo hi n0 {m} \<or> run_okg p q N R Hb lo hi n0 {m, next_idx m} \<or> run_okg p q N R Hb lo hi n0 {prev_idx m, m})"

definition USg where "USg p q N R Hb lo hi n0 band =
   Max (insert 0 ((UPB p q N R Hb lo hi) ` {m. PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m}))"

definition THg where "THg p dlf q N R Hb lo hi = lower (TH p q N R Hb lo hi) - dlf"

definition gterminal where "gterminal p dlf q N R Hb lo hi n0 band \<longleftrightarrow> USg p q N R Hb lo hi n0 band \<le> THg p dlf q N R Hb lo hi"

definition LLg where "LLg p q N R Hb lo hi n0 band =
   Max (insert 0 ((LOB p q N R Hb lo hi) ` {k. CP p q N R Hb lo hi k \<and> CO p lo hi n0 band k \<and>
     \<not> PMg p q N R Hb lo hi n0 k \<and> \<not> PMg p q N R Hb lo hi n0 (prev_idx k) \<and> \<not> PMg p q N R Hb lo hi n0 (next_idx k)}))"

definition gcand where "gcand p dlf q N R Hb lo hi n0 band m \<longleftrightarrow>
   PPg p q N R Hb lo hi m \<and> PO p lo hi n0 band m \<and> \<not> EXCg p q N R Hb lo hi n0 m \<and>
   THg p dlf q N R Hb lo hi \<le> UPB p q N R Hb lo hi m \<and>
   \<not> (0 < LLg p q N R Hb lo hi n0 band \<and> UPB p q N R Hb lo hi m < LLg p q N R Hb lo hi n0 band)"
