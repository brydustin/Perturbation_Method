theory GDCX_nc_197
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_3152: "gdc_sub None 3152"
  by (gdc_eval gdc_nc_3152)

lemma gdc_nc_3153: "gdc_sub None 3153"
  by (gdc_eval gdc_nc_3153)

lemma gdc_nc_3154: "gdc_sub None 3154"
  by (gdc_eval gdc_nc_3154)

lemma gdc_nc_3155: "gdc_sub None 3155"
  by (gdc_eval gdc_nc_3155)

lemma gdc_nc_3156: "gdc_sub None 3156"
  by (gdc_eval gdc_nc_3156)

lemma gdc_nc_3157: "gdc_sub None 3157"
  by (gdc_eval gdc_nc_3157)

lemma gdc_nc_3158: "gdc_sub None 3158"
  by (gdc_eval gdc_nc_3158)

lemma gdc_nc_3159: "gdc_sub None 3159"
  by (gdc_eval gdc_nc_3159)

lemma gdc_nc_3160: "gdc_sub None 3160"
  by (gdc_eval gdc_nc_3160)

lemma gdc_nc_3161: "gdc_sub None 3161"
  by (gdc_eval gdc_nc_3161)

lemma gdc_nc_3162: "gdc_sub None 3162"
  by (gdc_eval gdc_nc_3162)

lemma gdc_nc_3163: "gdc_sub None 3163"
  by (gdc_eval gdc_nc_3163)

lemma gdc_nc_3164: "gdc_sub None 3164"
  by (gdc_eval gdc_nc_3164)

lemma gdc_nc_3165: "gdc_sub None 3165"
  by (gdc_eval gdc_nc_3165)

lemma gdc_nc_3166: "gdc_sub None 3166"
  by (gdc_eval gdc_nc_3166)

lemma gdc_nc_3167: "gdc_sub None 3167"
  by (gdc_eval gdc_nc_3167)

lemma gupt_nc_197: "[3152..<3168] = [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]"
  by (simp add: upt_rec)

lemma gsec_nc_197: "\<forall>j\<in>{16 * 197..<16 * 197 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 197..<16 * 197 + 16}"
  then have "j \<in> set [3152..<3168]" unfolding set_upt by simp
  then have "j \<in> set [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]" unfolding gupt_nc_197 .
  then show "gdc_sub None j" using gdc_nc_3152 gdc_nc_3153 gdc_nc_3154 gdc_nc_3155 gdc_nc_3156 gdc_nc_3157 gdc_nc_3158 gdc_nc_3159 gdc_nc_3160 gdc_nc_3161 gdc_nc_3162 gdc_nc_3163 gdc_nc_3164 gdc_nc_3165 gdc_nc_3166 gdc_nc_3167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
