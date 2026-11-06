theory DCX_c30_011
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0176: "dc_sub dc_b30 176"
  by (dc_eval dc_c30_0176)

lemma dc_c30_0177: "dc_sub dc_b30 177"
  by (dc_eval dc_c30_0177)

lemma dc_c30_0178: "dc_sub dc_b30 178"
  by (dc_eval dc_c30_0178)

lemma dc_c30_0179: "dc_sub dc_b30 179"
  by (dc_eval dc_c30_0179)

lemma dc_c30_0180: "dc_sub dc_b30 180"
  by (dc_eval dc_c30_0180)

lemma dc_c30_0181: "dc_sub dc_b30 181"
  by (dc_eval dc_c30_0181)

lemma dc_c30_0182: "dc_sub dc_b30 182"
  by (dc_eval dc_c30_0182)

lemma dc_c30_0183: "dc_sub dc_b30 183"
  by (dc_eval dc_c30_0183)

lemma dc_c30_0184: "dc_sub dc_b30 184"
  by (dc_eval dc_c30_0184)

lemma dc_c30_0185: "dc_sub dc_b30 185"
  by (dc_eval dc_c30_0185)

lemma dc_c30_0186: "dc_sub dc_b30 186"
  by (dc_eval dc_c30_0186)

lemma dc_c30_0187: "dc_sub dc_b30 187"
  by (dc_eval dc_c30_0187)

lemma dc_c30_0188: "dc_sub dc_b30 188"
  by (dc_eval dc_c30_0188)

lemma dc_c30_0189: "dc_sub dc_b30 189"
  by (dc_eval dc_c30_0189)

lemma dc_c30_0190: "dc_sub dc_b30 190"
  by (dc_eval dc_c30_0190)

lemma dc_c30_0191: "dc_sub dc_b30 191"
  by (dc_eval dc_c30_0191)

lemma upt_c30_011: "[176..<192] = [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]"
  by (simp add: upt_rec)

lemma sec_c30_011: "\<forall>j\<in>{16 * 11..<16 * 11 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 11..<16 * 11 + 16}"
  then have "j \<in> set [176..<192]" unfolding set_upt by simp
  then have "j \<in> set [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]" unfolding upt_c30_011 .
  then show "dc_sub dc_b30 j" using dc_c30_0176 dc_c30_0177 dc_c30_0178 dc_c30_0179 dc_c30_0180 dc_c30_0181 dc_c30_0182 dc_c30_0183 dc_c30_0184 dc_c30_0185 dc_c30_0186 dc_c30_0187 dc_c30_0188 dc_c30_0189 dc_c30_0190 dc_c30_0191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
