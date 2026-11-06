theorem all_rules_transport:
  assumes "\<And>tm ts. tie_rule tm ts \<Longrightarrow> stops_within p N bd tm ts t D"
  shows "tie_rule tm' ts' \<Longrightarrow> stops_within p N bd tm' ts' (G t) D"
