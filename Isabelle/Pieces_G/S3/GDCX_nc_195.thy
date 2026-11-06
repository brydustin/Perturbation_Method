theory GDCX_nc_195
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3120: "gdc_sub None 3120"
  by (gdc_eval gdc_nc_3120)

lemma gdc_nc_3121: "gdc_sub None 3121"
  by (gdc_eval gdc_nc_3121)

lemma gdc_nc_3122: "gdc_sub None 3122"
  by (gdc_eval gdc_nc_3122)

lemma gdc_nc_3123: "gdc_sub None 3123"
  by (gdc_eval gdc_nc_3123)

lemma gdc_nc_3124: "gdc_sub None 3124"
  by (gdc_eval gdc_nc_3124)

lemma gdc_nc_3125: "gdc_sub None 3125"
  by (gdc_eval gdc_nc_3125)

lemma gdc_nc_3126: "gdc_sub None 3126"
  by (gdc_eval gdc_nc_3126)

lemma gdc_nc_3127: "gdc_sub None 3127"
  by (gdc_eval gdc_nc_3127)

lemma gdc_nc_3128: "gdc_sub None 3128"
  by (gdc_eval gdc_nc_3128)

lemma gdc_nc_3129: "gdc_sub None 3129"
  by (gdc_eval gdc_nc_3129)

lemma gdc_nc_3130: "gdc_sub None 3130"
  by (gdc_eval gdc_nc_3130)

lemma gdc_nc_3131: "gdc_sub None 3131"
  by (gdc_eval gdc_nc_3131)

lemma gdc_nc_3132: "gdc_sub None 3132"
  by (gdc_eval gdc_nc_3132)

lemma gdc_nc_3133: "gdc_sub None 3133"
  by (gdc_eval gdc_nc_3133)

lemma gdc_nc_3134: "gdc_sub None 3134"
  by (gdc_eval gdc_nc_3134)

lemma gdc_nc_3135: "gdc_sub None 3135"
  by (gdc_eval gdc_nc_3135)

lemma gupt_nc_195: "[3120..<3136] = [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]"
  by (simp add: upt_rec)

lemma gsec_nc_195: "\<forall>j\<in>{16 * 195..<16 * 195 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 195..<16 * 195 + 16}"
  then have "j \<in> set [3120..<3136]" unfolding set_upt by simp
  then have "j \<in> set [3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135]" unfolding gupt_nc_195 .
  then show "gdc_sub None j" using gdc_nc_3120 gdc_nc_3121 gdc_nc_3122 gdc_nc_3123 gdc_nc_3124 gdc_nc_3125 gdc_nc_3126 gdc_nc_3127 gdc_nc_3128 gdc_nc_3129 gdc_nc_3130 gdc_nc_3131 gdc_nc_3132 gdc_nc_3133 gdc_nc_3134 gdc_nc_3135
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
