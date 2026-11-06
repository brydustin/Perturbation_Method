theorem gstops_guarantee:
  assumes st: "gstops_within p N dl band tm ts t D" and tr: "tie_rule tm ts"
    and G: "\<And>j. j < N \<Longrightarrow> gam p j \<le> G"
    and dl: "2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2) * hM\<^sup>2 / 8 \<le> dl"
  shows "\<exists>n \<le> D. gelig p N dl band tm (grun p N dl band tm ts t n) t = {} \<and>
           (\<forall>\<phi>. pw p N (grun p N dl band tm ts t n) \<phi> > sqmax p N (grun p N dl band tm ts t n) / 100 \<longrightarrow>
              (\<exists>q y. lift q y \<and> (q = tm (fmains p N (grun p N dl band tm ts t n) t) mod M \<or> (q < M \<and> \<not> in_band band t q))
                 \<and> (\<forall>\<theta>. min \<phi> y \<le> \<theta> \<and> \<theta> \<le> max \<phi> y \<longrightarrow>
                      pw p N (grun p N dl band tm ts t n) \<theta> > sqmax p N (grun p N dl band tm ts t n) / 100 - 2 * dl)))"
