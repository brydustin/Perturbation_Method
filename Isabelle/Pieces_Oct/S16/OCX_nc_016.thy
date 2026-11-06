theory OCX_nc_016
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0256: "oc_sub None 256"
  by (oc_eval oc_nc_0256)

lemma oc_nc_0257: "oc_sub None 257"
  by (oc_eval oc_nc_0257)

lemma oc_nc_0258: "oc_sub None 258"
  by (oc_eval oc_nc_0258)

lemma oc_nc_0259: "oc_sub None 259"
  by (oc_eval oc_nc_0259)

lemma oc_nc_0260: "oc_sub None 260"
  by (oc_eval oc_nc_0260)

lemma oc_nc_0261: "oc_sub None 261"
  by (oc_eval oc_nc_0261)

lemma oc_nc_0262: "oc_sub None 262"
  by (oc_eval oc_nc_0262)

lemma oc_nc_0263: "oc_sub None 263"
  by (oc_eval oc_nc_0263)

lemma oc_nc_0264: "oc_sub None 264"
  by (oc_eval oc_nc_0264)

lemma oc_nc_0265: "oc_sub None 265"
  by (oc_eval oc_nc_0265)

lemma oc_nc_0266: "oc_sub None 266"
  by (oc_eval oc_nc_0266)

lemma oc_nc_0267: "oc_sub None 267"
  by (oc_eval oc_nc_0267)

lemma oc_nc_0268: "oc_sub None 268"
  by (oc_eval oc_nc_0268)

lemma oc_nc_0269: "oc_sub None 269"
  by (oc_eval oc_nc_0269)

lemma oc_nc_0270: "oc_sub None 270"
  by (oc_eval oc_nc_0270)

lemma oc_nc_0271: "oc_sub None 271"
  by (oc_eval oc_nc_0271)

lemma upt_nc_016: "[256..<272] = [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]"
  by (simp add: upt_rec)

lemma sec_nc_016: "\<forall>j\<in>{16 * 16..<16 * 16 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 16..<16 * 16 + 16}"
  then have "j \<in> set [256..<272]" unfolding set_upt by simp
  then have "j \<in> set [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]" unfolding upt_nc_016 .
  then show "oc_sub None j" using oc_nc_0256 oc_nc_0257 oc_nc_0258 oc_nc_0259 oc_nc_0260 oc_nc_0261 oc_nc_0262 oc_nc_0263 oc_nc_0264 oc_nc_0265 oc_nc_0266 oc_nc_0267 oc_nc_0268 oc_nc_0269 oc_nc_0270 oc_nc_0271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
