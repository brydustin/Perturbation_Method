theory GOCX_nc_015
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0240: "goc_sub None 240"
  by (goc_eval goc_nc_0240)

lemma goc_nc_0241: "goc_sub None 241"
  by (goc_eval goc_nc_0241)

lemma goc_nc_0242: "goc_sub None 242"
  by (goc_eval goc_nc_0242)

lemma goc_nc_0243: "goc_sub None 243"
  by (goc_eval goc_nc_0243)

lemma goc_nc_0244: "goc_sub None 244"
  by (goc_eval goc_nc_0244)

lemma goc_nc_0245: "goc_sub None 245"
  by (goc_eval goc_nc_0245)

lemma goc_nc_0246: "goc_sub None 246"
  by (goc_eval goc_nc_0246)

lemma goc_nc_0247: "goc_sub None 247"
  by (goc_eval goc_nc_0247)

lemma goc_nc_0248: "goc_sub None 248"
  by (goc_eval goc_nc_0248)

lemma goc_nc_0249: "goc_sub None 249"
  by (goc_eval goc_nc_0249)

lemma goc_nc_0250: "goc_sub None 250"
  by (goc_eval goc_nc_0250)

lemma goc_nc_0251: "goc_sub None 251"
  by (goc_eval goc_nc_0251)

lemma goc_nc_0252: "goc_sub None 252"
  by (goc_eval goc_nc_0252)

lemma goc_nc_0253: "goc_sub None 253"
  by (goc_eval goc_nc_0253)

lemma goc_nc_0254: "goc_sub None 254"
  by (goc_eval goc_nc_0254)

lemma goc_nc_0255: "goc_sub None 255"
  by (goc_eval goc_nc_0255)

lemma gupt_nc_015: "[240..<256] = [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]"
  by (simp add: upt_rec)

lemma gsec_nc_015: "\<forall>j\<in>{16 * 15..<16 * 15 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 15..<16 * 15 + 16}"
  then have "j \<in> set [240..<256]" unfolding set_upt by simp
  then have "j \<in> set [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]" unfolding gupt_nc_015 .
  then show "goc_sub None j" using goc_nc_0240 goc_nc_0241 goc_nc_0242 goc_nc_0243 goc_nc_0244 goc_nc_0245 goc_nc_0246 goc_nc_0247 goc_nc_0248 goc_nc_0249 goc_nc_0250 goc_nc_0251 goc_nc_0252 goc_nc_0253 goc_nc_0254 goc_nc_0255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
