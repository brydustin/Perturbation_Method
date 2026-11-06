theory OCX_nc_015
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0240: "oc_sub None 240"
  by (oc_eval oc_nc_0240)

lemma oc_nc_0241: "oc_sub None 241"
  by (oc_eval oc_nc_0241)

lemma oc_nc_0242: "oc_sub None 242"
  by (oc_eval oc_nc_0242)

lemma oc_nc_0243: "oc_sub None 243"
  by (oc_eval oc_nc_0243)

lemma oc_nc_0244: "oc_sub None 244"
  by (oc_eval oc_nc_0244)

lemma oc_nc_0245: "oc_sub None 245"
  by (oc_eval oc_nc_0245)

lemma oc_nc_0246: "oc_sub None 246"
  by (oc_eval oc_nc_0246)

lemma oc_nc_0247: "oc_sub None 247"
  by (oc_eval oc_nc_0247)

lemma oc_nc_0248: "oc_sub None 248"
  by (oc_eval oc_nc_0248)

lemma oc_nc_0249: "oc_sub None 249"
  by (oc_eval oc_nc_0249)

lemma oc_nc_0250: "oc_sub None 250"
  by (oc_eval oc_nc_0250)

lemma oc_nc_0251: "oc_sub None 251"
  by (oc_eval oc_nc_0251)

lemma oc_nc_0252: "oc_sub None 252"
  by (oc_eval oc_nc_0252)

lemma oc_nc_0253: "oc_sub None 253"
  by (oc_eval oc_nc_0253)

lemma oc_nc_0254: "oc_sub None 254"
  by (oc_eval oc_nc_0254)

lemma oc_nc_0255: "oc_sub None 255"
  by (oc_eval oc_nc_0255)

lemma upt_nc_015: "[240..<256] = [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]"
  by (simp add: upt_rec)

lemma sec_nc_015: "\<forall>j\<in>{16 * 15..<16 * 15 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 15..<16 * 15 + 16}"
  then have "j \<in> set [240..<256]" unfolding set_upt by simp
  then have "j \<in> set [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]" unfolding upt_nc_015 .
  then show "oc_sub None j" using oc_nc_0240 oc_nc_0241 oc_nc_0242 oc_nc_0243 oc_nc_0244 oc_nc_0245 oc_nc_0246 oc_nc_0247 oc_nc_0248 oc_nc_0249 oc_nc_0250 oc_nc_0251 oc_nc_0252 oc_nc_0253 oc_nc_0254 oc_nc_0255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
