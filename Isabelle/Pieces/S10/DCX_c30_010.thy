theory DCX_c30_010
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0160: "dc_sub dc_b30 160"
  by (dc_eval dc_c30_0160)

lemma dc_c30_0161: "dc_sub dc_b30 161"
  by (dc_eval dc_c30_0161)

lemma dc_c30_0162: "dc_sub dc_b30 162"
  by (dc_eval dc_c30_0162)

lemma dc_c30_0163: "dc_sub dc_b30 163"
  by (dc_eval dc_c30_0163)

lemma dc_c30_0164: "dc_sub dc_b30 164"
  by (dc_eval dc_c30_0164)

lemma dc_c30_0165: "dc_sub dc_b30 165"
  by (dc_eval dc_c30_0165)

lemma dc_c30_0166: "dc_sub dc_b30 166"
  by (dc_eval dc_c30_0166)

lemma dc_c30_0167: "dc_sub dc_b30 167"
  by (dc_eval dc_c30_0167)

lemma dc_c30_0168: "dc_sub dc_b30 168"
  by (dc_eval dc_c30_0168)

lemma dc_c30_0169: "dc_sub dc_b30 169"
  by (dc_eval dc_c30_0169)

lemma dc_c30_0170: "dc_sub dc_b30 170"
  by (dc_eval dc_c30_0170)

lemma dc_c30_0171: "dc_sub dc_b30 171"
  by (dc_eval dc_c30_0171)

lemma dc_c30_0172: "dc_sub dc_b30 172"
  by (dc_eval dc_c30_0172)

lemma dc_c30_0173: "dc_sub dc_b30 173"
  by (dc_eval dc_c30_0173)

lemma dc_c30_0174: "dc_sub dc_b30 174"
  by (dc_eval dc_c30_0174)

lemma dc_c30_0175: "dc_sub dc_b30 175"
  by (dc_eval dc_c30_0175)

lemma upt_c30_010: "[160..<176] = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]"
  by (simp add: upt_rec)

lemma sec_c30_010: "\<forall>j\<in>{16 * 10..<16 * 10 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 10..<16 * 10 + 16}"
  then have "j \<in> set [160..<176]" unfolding set_upt by simp
  then have "j \<in> set [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]" unfolding upt_c30_010 .
  then show "dc_sub dc_b30 j" using dc_c30_0160 dc_c30_0161 dc_c30_0162 dc_c30_0163 dc_c30_0164 dc_c30_0165 dc_c30_0166 dc_c30_0167 dc_c30_0168 dc_c30_0169 dc_c30_0170 dc_c30_0171 dc_c30_0172 dc_c30_0173 dc_c30_0174 dc_c30_0175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
