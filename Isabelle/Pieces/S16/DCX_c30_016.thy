theory DCX_c30_016
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0256: "dc_sub dc_b30 256"
  by (dc_eval dc_c30_0256)

lemma dc_c30_0257: "dc_sub dc_b30 257"
  by (dc_eval dc_c30_0257)

lemma dc_c30_0258: "dc_sub dc_b30 258"
  by (dc_eval dc_c30_0258)

lemma dc_c30_0259: "dc_sub dc_b30 259"
  by (dc_eval dc_c30_0259)

lemma dc_c30_0260: "dc_sub dc_b30 260"
  by (dc_eval dc_c30_0260)

lemma dc_c30_0261: "dc_sub dc_b30 261"
  by (dc_eval dc_c30_0261)

lemma dc_c30_0262: "dc_sub dc_b30 262"
  by (dc_eval dc_c30_0262)

lemma dc_c30_0263: "dc_sub dc_b30 263"
  by (dc_eval dc_c30_0263)

lemma dc_c30_0264: "dc_sub dc_b30 264"
  by (dc_eval dc_c30_0264)

lemma dc_c30_0265: "dc_sub dc_b30 265"
  by (dc_eval dc_c30_0265)

lemma dc_c30_0266: "dc_sub dc_b30 266"
  by (dc_eval dc_c30_0266)

lemma dc_c30_0267: "dc_sub dc_b30 267"
  by (dc_eval dc_c30_0267)

lemma dc_c30_0268: "dc_sub dc_b30 268"
  by (dc_eval dc_c30_0268)

lemma dc_c30_0269: "dc_sub dc_b30 269"
  by (dc_eval dc_c30_0269)

lemma dc_c30_0270: "dc_sub dc_b30 270"
  by (dc_eval dc_c30_0270)

lemma dc_c30_0271: "dc_sub dc_b30 271"
  by (dc_eval dc_c30_0271)

lemma upt_c30_016: "[256..<272] = [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]"
  by (simp add: upt_rec)

lemma sec_c30_016: "\<forall>j\<in>{16 * 16..<16 * 16 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 16..<16 * 16 + 16}"
  then have "j \<in> set [256..<272]" unfolding set_upt by simp
  then have "j \<in> set [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]" unfolding upt_c30_016 .
  then show "dc_sub dc_b30 j" using dc_c30_0256 dc_c30_0257 dc_c30_0258 dc_c30_0259 dc_c30_0260 dc_c30_0261 dc_c30_0262 dc_c30_0263 dc_c30_0264 dc_c30_0265 dc_c30_0266 dc_c30_0267 dc_c30_0268 dc_c30_0269 dc_c30_0270 dc_c30_0271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
