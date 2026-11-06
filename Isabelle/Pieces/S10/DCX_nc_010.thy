theory DCX_nc_010
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0160: "dc_sub None 160"
  by (dc_eval dc_nc_0160)

lemma dc_nc_0161: "dc_sub None 161"
  by (dc_eval dc_nc_0161)

lemma dc_nc_0162: "dc_sub None 162"
  by (dc_eval dc_nc_0162)

lemma dc_nc_0163: "dc_sub None 163"
  by (dc_eval dc_nc_0163)

lemma dc_nc_0164: "dc_sub None 164"
  by (dc_eval dc_nc_0164)

lemma dc_nc_0165: "dc_sub None 165"
  by (dc_eval dc_nc_0165)

lemma dc_nc_0166: "dc_sub None 166"
  by (dc_eval dc_nc_0166)

lemma dc_nc_0167: "dc_sub None 167"
  by (dc_eval dc_nc_0167)

lemma dc_nc_0168: "dc_sub None 168"
  by (dc_eval dc_nc_0168)

lemma dc_nc_0169: "dc_sub None 169"
  by (dc_eval dc_nc_0169)

lemma dc_nc_0170: "dc_sub None 170"
  by (dc_eval dc_nc_0170)

lemma dc_nc_0171: "dc_sub None 171"
  by (dc_eval dc_nc_0171)

lemma dc_nc_0172: "dc_sub None 172"
  by (dc_eval dc_nc_0172)

lemma dc_nc_0173: "dc_sub None 173"
  by (dc_eval dc_nc_0173)

lemma dc_nc_0174: "dc_sub None 174"
  by (dc_eval dc_nc_0174)

lemma dc_nc_0175: "dc_sub None 175"
  by (dc_eval dc_nc_0175)

lemma upt_nc_010: "[160..<176] = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]"
  by (simp add: upt_rec)

lemma sec_nc_010: "\<forall>j\<in>{16 * 10..<16 * 10 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 10..<16 * 10 + 16}"
  then have "j \<in> set [160..<176]" unfolding set_upt by simp
  then have "j \<in> set [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]" unfolding upt_nc_010 .
  then show "dc_sub None j" using dc_nc_0160 dc_nc_0161 dc_nc_0162 dc_nc_0163 dc_nc_0164 dc_nc_0165 dc_nc_0166 dc_nc_0167 dc_nc_0168 dc_nc_0169 dc_nc_0170 dc_nc_0171 dc_nc_0172 dc_nc_0173 dc_nc_0174 dc_nc_0175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
