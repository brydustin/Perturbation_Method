theory OCX_nc_010
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0160: "oc_sub None 160"
  by (oc_eval oc_nc_0160)

lemma oc_nc_0161: "oc_sub None 161"
  by (oc_eval oc_nc_0161)

lemma oc_nc_0162: "oc_sub None 162"
  by (oc_eval oc_nc_0162)

lemma oc_nc_0163: "oc_sub None 163"
  by (oc_eval oc_nc_0163)

lemma oc_nc_0164: "oc_sub None 164"
  by (oc_eval oc_nc_0164)

lemma oc_nc_0165: "oc_sub None 165"
  by (oc_eval oc_nc_0165)

lemma oc_nc_0166: "oc_sub None 166"
  by (oc_eval oc_nc_0166)

lemma oc_nc_0167: "oc_sub None 167"
  by (oc_eval oc_nc_0167)

lemma oc_nc_0168: "oc_sub None 168"
  by (oc_eval oc_nc_0168)

lemma oc_nc_0169: "oc_sub None 169"
  by (oc_eval oc_nc_0169)

lemma oc_nc_0170: "oc_sub None 170"
  by (oc_eval oc_nc_0170)

lemma oc_nc_0171: "oc_sub None 171"
  by (oc_eval oc_nc_0171)

lemma oc_nc_0172: "oc_sub None 172"
  by (oc_eval oc_nc_0172)

lemma oc_nc_0173: "oc_sub None 173"
  by (oc_eval oc_nc_0173)

lemma oc_nc_0174: "oc_sub None 174"
  by (oc_eval oc_nc_0174)

lemma oc_nc_0175: "oc_sub None 175"
  by (oc_eval oc_nc_0175)

lemma upt_nc_010: "[160..<176] = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]"
  by (simp add: upt_rec)

lemma sec_nc_010: "\<forall>j\<in>{16 * 10..<16 * 10 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 10..<16 * 10 + 16}"
  then have "j \<in> set [160..<176]" unfolding set_upt by simp
  then have "j \<in> set [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]" unfolding upt_nc_010 .
  then show "oc_sub None j" using oc_nc_0160 oc_nc_0161 oc_nc_0162 oc_nc_0163 oc_nc_0164 oc_nc_0165 oc_nc_0166 oc_nc_0167 oc_nc_0168 oc_nc_0169 oc_nc_0170 oc_nc_0171 oc_nc_0172 oc_nc_0173 oc_nc_0174 oc_nc_0175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
