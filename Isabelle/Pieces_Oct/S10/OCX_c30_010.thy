theory OCX_c30_010
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0160: "oc_sub oc_b30 160"
  by (oc_eval oc_c30_0160)

lemma oc_c30_0161: "oc_sub oc_b30 161"
  by (oc_eval oc_c30_0161)

lemma oc_c30_0162: "oc_sub oc_b30 162"
  by (oc_eval oc_c30_0162)

lemma oc_c30_0163: "oc_sub oc_b30 163"
  by (oc_eval oc_c30_0163)

lemma oc_c30_0164: "oc_sub oc_b30 164"
  by (oc_eval oc_c30_0164)

lemma oc_c30_0165: "oc_sub oc_b30 165"
  by (oc_eval oc_c30_0165)

lemma oc_c30_0166: "oc_sub oc_b30 166"
  by (oc_eval oc_c30_0166)

lemma oc_c30_0167: "oc_sub oc_b30 167"
  by (oc_eval oc_c30_0167)

lemma oc_c30_0168: "oc_sub oc_b30 168"
  by (oc_eval oc_c30_0168)

lemma oc_c30_0169: "oc_sub oc_b30 169"
  by (oc_eval oc_c30_0169)

lemma oc_c30_0170: "oc_sub oc_b30 170"
  by (oc_eval oc_c30_0170)

lemma oc_c30_0171: "oc_sub oc_b30 171"
  by (oc_eval oc_c30_0171)

lemma oc_c30_0172: "oc_sub oc_b30 172"
  by (oc_eval oc_c30_0172)

lemma oc_c30_0173: "oc_sub oc_b30 173"
  by (oc_eval oc_c30_0173)

lemma oc_c30_0174: "oc_sub oc_b30 174"
  by (oc_eval oc_c30_0174)

lemma oc_c30_0175: "oc_sub oc_b30 175"
  by (oc_eval oc_c30_0175)

lemma upt_c30_010: "[160..<176] = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]"
  by (simp add: upt_rec)

lemma sec_c30_010: "\<forall>j\<in>{16 * 10..<16 * 10 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 10..<16 * 10 + 16}"
  then have "j \<in> set [160..<176]" unfolding set_upt by simp
  then have "j \<in> set [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]" unfolding upt_c30_010 .
  then show "oc_sub oc_b30 j" using oc_c30_0160 oc_c30_0161 oc_c30_0162 oc_c30_0163 oc_c30_0164 oc_c30_0165 oc_c30_0166 oc_c30_0167 oc_c30_0168 oc_c30_0169 oc_c30_0170 oc_c30_0171 oc_c30_0172 oc_c30_0173 oc_c30_0174 oc_c30_0175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
