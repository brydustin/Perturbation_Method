theory OCX_c30_011
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0176: "oc_sub oc_b30 176"
  by (oc_eval oc_c30_0176)

lemma oc_c30_0177: "oc_sub oc_b30 177"
  by (oc_eval oc_c30_0177)

lemma oc_c30_0178: "oc_sub oc_b30 178"
  by (oc_eval oc_c30_0178)

lemma oc_c30_0179: "oc_sub oc_b30 179"
  by (oc_eval oc_c30_0179)

lemma oc_c30_0180: "oc_sub oc_b30 180"
  by (oc_eval oc_c30_0180)

lemma oc_c30_0181: "oc_sub oc_b30 181"
  by (oc_eval oc_c30_0181)

lemma oc_c30_0182: "oc_sub oc_b30 182"
  by (oc_eval oc_c30_0182)

lemma oc_c30_0183: "oc_sub oc_b30 183"
  by (oc_eval oc_c30_0183)

lemma oc_c30_0184: "oc_sub oc_b30 184"
  by (oc_eval oc_c30_0184)

lemma oc_c30_0185: "oc_sub oc_b30 185"
  by (oc_eval oc_c30_0185)

lemma oc_c30_0186: "oc_sub oc_b30 186"
  by (oc_eval oc_c30_0186)

lemma oc_c30_0187: "oc_sub oc_b30 187"
  by (oc_eval oc_c30_0187)

lemma oc_c30_0188: "oc_sub oc_b30 188"
  by (oc_eval oc_c30_0188)

lemma oc_c30_0189: "oc_sub oc_b30 189"
  by (oc_eval oc_c30_0189)

lemma oc_c30_0190: "oc_sub oc_b30 190"
  by (oc_eval oc_c30_0190)

lemma oc_c30_0191: "oc_sub oc_b30 191"
  by (oc_eval oc_c30_0191)

lemma upt_c30_011: "[176..<192] = [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]"
  by (simp add: upt_rec)

lemma sec_c30_011: "\<forall>j\<in>{16 * 11..<16 * 11 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 11..<16 * 11 + 16}"
  then have "j \<in> set [176..<192]" unfolding set_upt by simp
  then have "j \<in> set [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]" unfolding upt_c30_011 .
  then show "oc_sub oc_b30 j" using oc_c30_0176 oc_c30_0177 oc_c30_0178 oc_c30_0179 oc_c30_0180 oc_c30_0181 oc_c30_0182 oc_c30_0183 oc_c30_0184 oc_c30_0185 oc_c30_0186 oc_c30_0187 oc_c30_0188 oc_c30_0189 oc_c30_0190 oc_c30_0191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
