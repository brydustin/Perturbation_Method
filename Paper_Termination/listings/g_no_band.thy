corollary guarantee_no_band:
  assumes stop: "gelig p N dl None tm c t = {}" and tr: "tie_rule tm ts"
    and dl: "Hc c p N * hM\<^sup>2 / 8 \<le> dl"
    and phi: "pw p N c \<phi> > sqmax p N c / 100"
  shows "\<exists>y. lift (tm (fmains p N c t)) y
           \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow> pw p N c \<theta> > sqmax p N c / 100 - 2 * dl)"
