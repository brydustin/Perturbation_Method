theorem Hc_le_norm:
  assumes G: "\<And>j. j < N \<Longrightarrow> gam p j \<le> G" and n: "nrm N c \<le> real N"
  shows "Hc c p N \<le> 2 * (real N)\<^sup>2 * (G + 2 * G\<^sup>2)"
