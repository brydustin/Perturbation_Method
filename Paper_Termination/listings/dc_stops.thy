definition dc_stops :: "real option \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "dc_stops bd t D \<longleftrightarrow> (\<forall>tm ts. tie_rule tm ts \<longrightarrow> stops_within dcp 9 bd tm ts t D)"
