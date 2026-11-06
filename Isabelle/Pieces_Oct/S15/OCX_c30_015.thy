theory OCX_c30_015
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0240: "oc_sub oc_b30 240"
  by (oc_eval oc_c30_0240)

lemma oc_c30_0241: "oc_sub oc_b30 241"
  by (oc_eval oc_c30_0241)

lemma oc_c30_0242: "oc_sub oc_b30 242"
  by (oc_eval oc_c30_0242)

lemma oc_c30_0243: "oc_sub oc_b30 243"
  by (oc_eval oc_c30_0243)

lemma oc_c30_0244: "oc_sub oc_b30 244"
  by (oc_eval oc_c30_0244)

lemma oc_c30_0245: "oc_sub oc_b30 245"
  by (oc_eval oc_c30_0245)

lemma oc_c30_0246: "oc_sub oc_b30 246"
  by (oc_eval oc_c30_0246)

lemma oc_c30_0247: "oc_sub oc_b30 247"
  by (oc_eval oc_c30_0247)

lemma oc_c30_0248: "oc_sub oc_b30 248"
  by (oc_eval oc_c30_0248)

lemma oc_c30_0249: "oc_sub oc_b30 249"
  by (oc_eval oc_c30_0249)

lemma oc_c30_0250: "oc_sub oc_b30 250"
  by (oc_eval oc_c30_0250)

lemma oc_c30_0251: "oc_sub oc_b30 251"
  by (oc_eval oc_c30_0251)

lemma oc_c30_0252: "oc_sub oc_b30 252"
  by (oc_eval oc_c30_0252)

lemma oc_c30_0253: "oc_sub oc_b30 253"
  by (oc_eval oc_c30_0253)

lemma oc_c30_0254: "oc_sub oc_b30 254"
  by (oc_eval oc_c30_0254)

lemma oc_c30_0255: "oc_sub oc_b30 255"
  by (oc_eval oc_c30_0255)

lemma upt_c30_015: "[240..<256] = [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]"
  by (simp add: upt_rec)

lemma sec_c30_015: "\<forall>j\<in>{16 * 15..<16 * 15 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 15..<16 * 15 + 16}"
  then have "j \<in> set [240..<256]" unfolding set_upt by simp
  then have "j \<in> set [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]" unfolding upt_c30_015 .
  then show "oc_sub oc_b30 j" using oc_c30_0240 oc_c30_0241 oc_c30_0242 oc_c30_0243 oc_c30_0244 oc_c30_0245 oc_c30_0246 oc_c30_0247 oc_c30_0248 oc_c30_0249 oc_c30_0250 oc_c30_0251 oc_c30_0252 oc_c30_0253 oc_c30_0254 oc_c30_0255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
