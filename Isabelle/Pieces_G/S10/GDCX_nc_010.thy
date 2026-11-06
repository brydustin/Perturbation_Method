theory GDCX_nc_010
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0160: "gdc_sub None 160"
  by (gdc_eval gdc_nc_0160)

lemma gdc_nc_0161: "gdc_sub None 161"
  by (gdc_eval gdc_nc_0161)

lemma gdc_nc_0162: "gdc_sub None 162"
  by (gdc_eval gdc_nc_0162)

lemma gdc_nc_0163: "gdc_sub None 163"
  by (gdc_eval gdc_nc_0163)

lemma gdc_nc_0164: "gdc_sub None 164"
  by (gdc_eval gdc_nc_0164)

lemma gdc_nc_0165: "gdc_sub None 165"
  by (gdc_eval gdc_nc_0165)

lemma gdc_nc_0166: "gdc_sub None 166"
  by (gdc_eval gdc_nc_0166)

lemma gdc_nc_0167: "gdc_sub None 167"
  by (gdc_eval gdc_nc_0167)

lemma gdc_nc_0168: "gdc_sub None 168"
  by (gdc_eval gdc_nc_0168)

lemma gdc_nc_0169: "gdc_sub None 169"
  by (gdc_eval gdc_nc_0169)

lemma gdc_nc_0170: "gdc_sub None 170"
  by (gdc_eval gdc_nc_0170)

lemma gdc_nc_0171: "gdc_sub None 171"
  by (gdc_eval gdc_nc_0171)

lemma gdc_nc_0172: "gdc_sub None 172"
  by (gdc_eval gdc_nc_0172)

lemma gdc_nc_0173: "gdc_sub None 173"
  by (gdc_eval gdc_nc_0173)

lemma gdc_nc_0174: "gdc_sub None 174"
  by (gdc_eval gdc_nc_0174)

lemma gdc_nc_0175: "gdc_sub None 175"
  by (gdc_eval gdc_nc_0175)

lemma gupt_nc_010: "[160..<176] = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]"
  by (simp add: upt_rec)

lemma gsec_nc_010: "\<forall>j\<in>{16 * 10..<16 * 10 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 10..<16 * 10 + 16}"
  then have "j \<in> set [160..<176]" unfolding set_upt by simp
  then have "j \<in> set [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]" unfolding gupt_nc_010 .
  then show "gdc_sub None j" using gdc_nc_0160 gdc_nc_0161 gdc_nc_0162 gdc_nc_0163 gdc_nc_0164 gdc_nc_0165 gdc_nc_0166 gdc_nc_0167 gdc_nc_0168 gdc_nc_0169 gdc_nc_0170 gdc_nc_0171 gdc_nc_0172 gdc_nc_0173 gdc_nc_0174 gdc_nc_0175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
