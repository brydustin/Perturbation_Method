theorem dc_stops_all:
  assumes base: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> pi/4 \<Longrightarrow> dc_stops bd t D"
  shows "dc_stops bd t D"
