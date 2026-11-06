theory OCX_c30_016
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0256: "oc_sub oc_b30 256"
  by (oc_eval oc_c30_0256)

lemma oc_c30_0257: "oc_sub oc_b30 257"
  by (oc_eval oc_c30_0257)

lemma oc_c30_0258: "oc_sub oc_b30 258"
  by (oc_eval oc_c30_0258)

lemma oc_c30_0259: "oc_sub oc_b30 259"
  by (oc_eval oc_c30_0259)

lemma oc_c30_0260: "oc_sub oc_b30 260"
  by (oc_eval oc_c30_0260)

lemma oc_c30_0261: "oc_sub oc_b30 261"
  by (oc_eval oc_c30_0261)

lemma oc_c30_0262: "oc_sub oc_b30 262"
  by (oc_eval oc_c30_0262)

lemma oc_c30_0263: "oc_sub oc_b30 263"
  by (oc_eval oc_c30_0263)

lemma oc_c30_0264: "oc_sub oc_b30 264"
  by (oc_eval oc_c30_0264)

lemma oc_c30_0265: "oc_sub oc_b30 265"
  by (oc_eval oc_c30_0265)

lemma oc_c30_0266: "oc_sub oc_b30 266"
  by (oc_eval oc_c30_0266)

lemma oc_c30_0267: "oc_sub oc_b30 267"
  by (oc_eval oc_c30_0267)

lemma oc_c30_0268: "oc_sub oc_b30 268"
  by (oc_eval oc_c30_0268)

lemma oc_c30_0269: "oc_sub oc_b30 269"
  by (oc_eval oc_c30_0269)

lemma oc_c30_0270: "oc_sub oc_b30 270"
  by (oc_eval oc_c30_0270)

lemma oc_c30_0271: "oc_sub oc_b30 271"
  by (oc_eval oc_c30_0271)

lemma upt_c30_016: "[256..<272] = [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]"
  by (simp add: upt_rec)

lemma sec_c30_016: "\<forall>j\<in>{16 * 16..<16 * 16 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 16..<16 * 16 + 16}"
  then have "j \<in> set [256..<272]" unfolding set_upt by simp
  then have "j \<in> set [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271]" unfolding upt_c30_016 .
  then show "oc_sub oc_b30 j" using oc_c30_0256 oc_c30_0257 oc_c30_0258 oc_c30_0259 oc_c30_0260 oc_c30_0261 oc_c30_0262 oc_c30_0263 oc_c30_0264 oc_c30_0265 oc_c30_0266 oc_c30_0267 oc_c30_0268 oc_c30_0269 oc_c30_0270 oc_c30_0271
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
