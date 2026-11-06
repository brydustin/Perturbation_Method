theory GOCX_nc_016
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0256: "goc_sub None 256"
  by (goc_eval goc_nc_0256)

lemma goc_nc_0257: "goc_sub None 257"
  by (goc_eval goc_nc_0257)

lemma goc_nc_0258: "goc_sub None 258"
  by (goc_eval goc_nc_0258)

lemma goc_nc_0259: "goc_sub None 259"
  by (goc_eval goc_nc_0259)

lemma goc_nc_0260: "goc_sub None 260"
  by (goc_eval goc_nc_0260)

lemma goc_nc_0261: "goc_sub None 261"
  by (goc_eval goc_nc_0261)

lemma goc_nc_0262: "goc_sub None 262"
  by (goc_eval goc_nc_0262)

lemma goc_nc_0263: "goc_sub None 263"
  by (goc_eval goc_nc_0263)

lemma goc_nc_0264: "goc_sub None 264"
  by (goc_eval goc_nc_0264)

lemma goc_nc_0265: "goc_sub None 265"
  by (goc_eval goc_nc_0265)

lemma goc_nc_0266: "goc_sub None 266"
  by (goc_eval goc_nc_0266)

lemma goc_nc_0267: "goc_sub None 267"
  by (goc_eval goc_nc_0267)

lemma goc_nc_0268: "goc_sub None 268"
  by (goc_eval goc_nc_0268)

lemma goc_nc_0269: "goc_sub None 269"
  by (goc_eval goc_nc_0269)

lemma goc_nc_0270: "goc_sub None 270"
  by (goc_eval goc_nc_0270)

lemma goc_nc_0271: "goc_sub None 271"
  by (goc_eval goc_nc_0271)

lemma gupt_nc_016: "[256..<272] = [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]"
  by (simp add: upt_rec)

lemma gsec_nc_016: "\<forall>j\<in>{16 * 16..<16 * 16 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 16..<16 * 16 + 16}"
  then have "j \<in> set [256..<272]" unfolding set_upt by simp
  then have "j \<in> set [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]" unfolding gupt_nc_016 .
  then show "goc_sub None j" using goc_nc_0256 goc_nc_0257 goc_nc_0258 goc_nc_0259 goc_nc_0260 goc_nc_0261 goc_nc_0262 goc_nc_0263 goc_nc_0264 goc_nc_0265 goc_nc_0266 goc_nc_0267 goc_nc_0268 goc_nc_0269 goc_nc_0270 goc_nc_0271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
