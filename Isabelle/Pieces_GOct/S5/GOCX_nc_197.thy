theory GOCX_nc_197
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_3152: "goc_sub None 3152"
  by (goc_eval goc_nc_3152)

lemma goc_nc_3153: "goc_sub None 3153"
  by (goc_eval goc_nc_3153)

lemma goc_nc_3154: "goc_sub None 3154"
  by (goc_eval goc_nc_3154)

lemma goc_nc_3155: "goc_sub None 3155"
  by (goc_eval goc_nc_3155)

lemma goc_nc_3156: "goc_sub None 3156"
  by (goc_eval goc_nc_3156)

lemma goc_nc_3157: "goc_sub None 3157"
  by (goc_eval goc_nc_3157)

lemma goc_nc_3158: "goc_sub None 3158"
  by (goc_eval goc_nc_3158)

lemma goc_nc_3159: "goc_sub None 3159"
  by (goc_eval goc_nc_3159)

lemma goc_nc_3160: "goc_sub None 3160"
  by (goc_eval goc_nc_3160)

lemma goc_nc_3161: "goc_sub None 3161"
  by (goc_eval goc_nc_3161)

lemma goc_nc_3162: "goc_sub None 3162"
  by (goc_eval goc_nc_3162)

lemma goc_nc_3163: "goc_sub None 3163"
  by (goc_eval goc_nc_3163)

lemma goc_nc_3164: "goc_sub None 3164"
  by (goc_eval goc_nc_3164)

lemma goc_nc_3165: "goc_sub None 3165"
  by (goc_eval goc_nc_3165)

lemma goc_nc_3166: "goc_sub None 3166"
  by (goc_eval goc_nc_3166)

lemma goc_nc_3167: "goc_sub None 3167"
  by (goc_eval goc_nc_3167)

lemma gupt_nc_197: "[3152..<3168] = [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]"
  by (simp add: upt_rec)

lemma gsec_nc_197: "\<forall>j\<in>{16 * 197..<16 * 197 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 197..<16 * 197 + 16}"
  then have "j \<in> set [3152..<3168]" unfolding set_upt by simp
  then have "j \<in> set [3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167]" unfolding gupt_nc_197 .
  then show "goc_sub None j" using goc_nc_3152 goc_nc_3153 goc_nc_3154 goc_nc_3155 goc_nc_3156 goc_nc_3157 goc_nc_3158 goc_nc_3159 goc_nc_3160 goc_nc_3161 goc_nc_3162 goc_nc_3163 goc_nc_3164 goc_nc_3165 goc_nc_3166 goc_nc_3167
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
