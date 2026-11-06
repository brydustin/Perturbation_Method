theorem verify_sound:
  assumes IN: "1 / real N \<in>\<^sub>r IN" and bd: "band_in bd band" and tr: "tie_rule tm ts"
  shows "verify p q N IN n0f band Dmax wmin f lo hi \<sigma> \<Longrightarrow> length \<sigma> \<le> Dmax \<Longrightarrow>
         real_of_float lo \<le> t \<Longrightarrow> t \<le> real_of_float hi \<Longrightarrow>
         corrs (fpos q) N bd tm ts t (length \<sigma>) = \<sigma> \<Longrightarrow>
         stops_within (fpos q) N bd tm ts t Dmax"
