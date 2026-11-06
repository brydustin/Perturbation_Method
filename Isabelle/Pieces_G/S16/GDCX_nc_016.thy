theory GDCX_nc_016
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0256: "gdc_sub None 256"
  by (gdc_eval gdc_nc_0256)

lemma gdc_nc_0257: "gdc_sub None 257"
  by (gdc_eval gdc_nc_0257)

lemma gdc_nc_0258: "gdc_sub None 258"
  by (gdc_eval gdc_nc_0258)

lemma gdc_nc_0259: "gdc_sub None 259"
  by (gdc_eval gdc_nc_0259)

lemma gdc_nc_0260: "gdc_sub None 260"
  by (gdc_eval gdc_nc_0260)

lemma gdc_nc_0261: "gdc_sub None 261"
  by (gdc_eval gdc_nc_0261)

lemma gdc_nc_0262: "gdc_sub None 262"
  by (gdc_eval gdc_nc_0262)

lemma gdc_nc_0263: "gdc_sub None 263"
  by (gdc_eval gdc_nc_0263)

lemma gdc_nc_0264: "gdc_sub None 264"
  by (gdc_eval gdc_nc_0264)

lemma gdc_nc_0265: "gdc_sub None 265"
  by (gdc_eval gdc_nc_0265)

lemma gdc_nc_0266: "gdc_sub None 266"
  by (gdc_eval gdc_nc_0266)

lemma gdc_nc_0267: "gdc_sub None 267"
  by (gdc_eval gdc_nc_0267)

lemma gdc_nc_0268: "gdc_sub None 268"
  by (gdc_eval gdc_nc_0268)

lemma gdc_nc_0269: "gdc_sub None 269"
  by (gdc_eval gdc_nc_0269)

lemma gdc_nc_0270: "gdc_sub None 270"
  by (gdc_eval gdc_nc_0270)

lemma gdc_nc_0271: "gdc_sub None 271"
  by (gdc_eval gdc_nc_0271)

lemma gupt_nc_016: "[256..<272] = [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]"
  by (simp add: upt_rec)

lemma gsec_nc_016: "\<forall>j\<in>{16 * 16..<16 * 16 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 16..<16 * 16 + 16}"
  then have "j \<in> set [256..<272]" unfolding set_upt by simp
  then have "j \<in> set [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]" unfolding gupt_nc_016 .
  then show "gdc_sub None j" using gdc_nc_0256 gdc_nc_0257 gdc_nc_0258 gdc_nc_0259 gdc_nc_0260 gdc_nc_0261 gdc_nc_0262 gdc_nc_0263 gdc_nc_0264 gdc_nc_0265 gdc_nc_0266 gdc_nc_0267 gdc_nc_0268 gdc_nc_0269 gdc_nc_0270 gdc_nc_0271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
