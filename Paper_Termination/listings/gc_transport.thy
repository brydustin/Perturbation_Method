theorem gall_rules_transport:
  assumes "\<And>tm ts. tie_rule tm ts \<Longrightarrow> gstops_within p N dl bd tm ts t D"
  shows "tie_rule tm' ts' \<Longrightarrow> gstops_within p N dl bd tm' ts' (G t) D"
