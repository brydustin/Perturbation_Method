theory GOCX_nc_010
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0160: "goc_sub None 160"
  by (goc_eval goc_nc_0160)

lemma goc_nc_0161: "goc_sub None 161"
  by (goc_eval goc_nc_0161)

lemma goc_nc_0162: "goc_sub None 162"
  by (goc_eval goc_nc_0162)

lemma goc_nc_0163: "goc_sub None 163"
  by (goc_eval goc_nc_0163)

lemma goc_nc_0164: "goc_sub None 164"
  by (goc_eval goc_nc_0164)

lemma goc_nc_0165: "goc_sub None 165"
  by (goc_eval goc_nc_0165)

lemma goc_nc_0166: "goc_sub None 166"
  by (goc_eval goc_nc_0166)

lemma goc_nc_0167: "goc_sub None 167"
  by (goc_eval goc_nc_0167)

lemma goc_nc_0168: "goc_sub None 168"
  by (goc_eval goc_nc_0168)

lemma goc_nc_0169: "goc_sub None 169"
  by (goc_eval goc_nc_0169)

lemma goc_nc_0170: "goc_sub None 170"
  by (goc_eval goc_nc_0170)

lemma goc_nc_0171: "goc_sub None 171"
  by (goc_eval goc_nc_0171)

lemma goc_nc_0172: "goc_sub None 172"
  by (goc_eval goc_nc_0172)

lemma goc_nc_0173: "goc_sub None 173"
  by (goc_eval goc_nc_0173)

lemma goc_nc_0174: "goc_sub None 174"
  by (goc_eval goc_nc_0174)

lemma goc_nc_0175: "goc_sub None 175"
  by (goc_eval goc_nc_0175)

lemma gupt_nc_010: "[160..<176] = [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]"
  by (simp add: upt_rec)

lemma gsec_nc_010: "\<forall>j\<in>{16 * 10..<16 * 10 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 10..<16 * 10 + 16}"
  then have "j \<in> set [160..<176]" unfolding set_upt by simp
  then have "j \<in> set [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]" unfolding gupt_nc_010 .
  then show "goc_sub None j" using goc_nc_0160 goc_nc_0161 goc_nc_0162 goc_nc_0163 goc_nc_0164 goc_nc_0165 goc_nc_0166 goc_nc_0167 goc_nc_0168 goc_nc_0169 goc_nc_0170 goc_nc_0171 goc_nc_0172 goc_nc_0173 goc_nc_0174 goc_nc_0175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
