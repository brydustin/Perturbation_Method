theorem circular_floor_20: "1614 / 10000 * maxAll cv \<le> maxQ 20 cv"
  by (rule floor_from_check [OF check20 _ K20]) simp_all

theorem circular_floor_30: "1286 / 10000 * maxAll cv \<le> maxQ 30 cv"
  by (rule floor_from_check [OF check30 _ K30]) simp_all


theorem circular_cannot_stop_20: "\<exists>j<32. cv j \<noteq> 0 \<Longrightarrow> \<not> maxQ 20 cv \<le> 1/10 * maxAll cv"
  by (rule no_stop_from_check [OF check20 _ K20]) simp_all

theorem circular_cannot_stop_30: "\<exists>j<32. cv j \<noteq> 0 \<Longrightarrow> \<not> maxQ 30 cv \<le> 1/10 * maxAll cv"
  by (rule no_stop_from_check [OF check30 _ K30]) simp_all
