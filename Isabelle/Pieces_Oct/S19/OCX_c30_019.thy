theory OCX_c30_019
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0304: "oc_sub oc_b30 304"
  by (oc_eval oc_c30_0304)

lemma oc_c30_0305: "oc_sub oc_b30 305"
  by (oc_eval oc_c30_0305)

lemma oc_c30_0306: "oc_sub oc_b30 306"
  by (oc_eval oc_c30_0306)

lemma oc_c30_0307: "oc_sub oc_b30 307"
  by (oc_eval oc_c30_0307)

lemma oc_c30_0308: "oc_sub oc_b30 308"
  by (oc_eval oc_c30_0308)

lemma oc_c30_0309: "oc_sub oc_b30 309"
  by (oc_eval oc_c30_0309)

lemma oc_c30_0310: "oc_sub oc_b30 310"
  by (oc_eval oc_c30_0310)

lemma oc_c30_0311: "oc_sub oc_b30 311"
  by (oc_eval oc_c30_0311)

lemma oc_c30_0312: "oc_sub oc_b30 312"
  by (oc_eval oc_c30_0312)

lemma oc_c30_0313: "oc_sub oc_b30 313"
  by (oc_eval oc_c30_0313)

lemma oc_c30_0314: "oc_sub oc_b30 314"
  by (oc_eval oc_c30_0314)

lemma oc_c30_0315: "oc_sub oc_b30 315"
  by (oc_eval oc_c30_0315)

lemma oc_c30_0316: "oc_sub oc_b30 316"
  by (oc_eval oc_c30_0316)

lemma oc_c30_0317: "oc_sub oc_b30 317"
  by (oc_eval oc_c30_0317)

lemma oc_c30_0318: "oc_sub oc_b30 318"
  by (oc_eval oc_c30_0318)

lemma oc_c30_0319: "oc_sub oc_b30 319"
  by (oc_eval oc_c30_0319)

lemma upt_c30_019: "[304..<320] = [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]"
  by (simp add: upt_rec)

lemma sec_c30_019: "\<forall>j\<in>{16 * 19..<16 * 19 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 19..<16 * 19 + 16}"
  then have "j \<in> set [304..<320]" unfolding set_upt by simp
  then have "j \<in> set [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]" unfolding upt_c30_019 .
  then show "oc_sub oc_b30 j" using oc_c30_0304 oc_c30_0305 oc_c30_0306 oc_c30_0307 oc_c30_0308 oc_c30_0309 oc_c30_0310 oc_c30_0311 oc_c30_0312 oc_c30_0313 oc_c30_0314 oc_c30_0315 oc_c30_0316 oc_c30_0317 oc_c30_0318 oc_c30_0319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
