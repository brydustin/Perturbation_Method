theory GOCX_nc_195
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3120: "goc_sub None 3120"
  by (goc_eval goc_nc_3120)

lemma goc_nc_3121: "goc_sub None 3121"
  by (goc_eval goc_nc_3121)

lemma goc_nc_3122: "goc_sub None 3122"
  by (goc_eval goc_nc_3122)

lemma goc_nc_3123: "goc_sub None 3123"
  by (goc_eval goc_nc_3123)

lemma goc_nc_3124: "goc_sub None 3124"
  by (goc_eval goc_nc_3124)

lemma goc_nc_3125: "goc_sub None 3125"
  by (goc_eval goc_nc_3125)

lemma goc_nc_3126: "goc_sub None 3126"
  by (goc_eval goc_nc_3126)

lemma goc_nc_3127: "goc_sub None 3127"
  by (goc_eval goc_nc_3127)

lemma goc_nc_3128: "goc_sub None 3128"
  by (goc_eval goc_nc_3128)

lemma goc_nc_3129: "goc_sub None 3129"
  by (goc_eval goc_nc_3129)

lemma goc_nc_3130: "goc_sub None 3130"
  by (goc_eval goc_nc_3130)

lemma goc_nc_3131: "goc_sub None 3131"
  by (goc_eval goc_nc_3131)

lemma goc_nc_3132: "goc_sub None 3132"
  by (goc_eval goc_nc_3132)

lemma goc_nc_3133: "goc_sub None 3133"
  by (goc_eval goc_nc_3133)

lemma goc_nc_3134: "goc_sub None 3134"
  by (goc_eval goc_nc_3134)

lemma goc_nc_3135: "goc_sub None 3135"
  by (goc_eval goc_nc_3135)

lemma gupt_nc_195: "[3120..<3136] = [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]"
  by (simp add: upt_rec)

lemma gsec_nc_195: "\<forall>j\<in>{16 * 195..<16 * 195 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 195..<16 * 195 + 16}"
  then have "j \<in> set [3120..<3136]" unfolding set_upt by simp
  then have "j \<in> set [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]" unfolding gupt_nc_195 .
  then show "goc_sub None j" using goc_nc_3120 goc_nc_3121 goc_nc_3122 goc_nc_3123 goc_nc_3124 goc_nc_3125 goc_nc_3126 goc_nc_3127 goc_nc_3128 goc_nc_3129 goc_nc_3130 goc_nc_3131 goc_nc_3132 goc_nc_3133 goc_nc_3134 goc_nc_3135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
