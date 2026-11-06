theory OCX_c30_140
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2240: "oc_sub oc_b30 2240"
  by (oc_eval oc_c30_2240)

lemma oc_c30_2241: "oc_sub oc_b30 2241"
  by (oc_eval oc_c30_2241)

lemma oc_c30_2242: "oc_sub oc_b30 2242"
  by (oc_eval oc_c30_2242)

lemma oc_c30_2243: "oc_sub oc_b30 2243"
  by (oc_eval oc_c30_2243)

lemma oc_c30_2244: "oc_sub oc_b30 2244"
  by (oc_eval oc_c30_2244)

lemma oc_c30_2245: "oc_sub oc_b30 2245"
  by (oc_eval oc_c30_2245)

lemma oc_c30_2246: "oc_sub oc_b30 2246"
  by (oc_eval oc_c30_2246)

lemma oc_c30_2247: "oc_sub oc_b30 2247"
  by (oc_eval oc_c30_2247)

lemma oc_c30_2248: "oc_sub oc_b30 2248"
  by (oc_eval oc_c30_2248)

lemma oc_c30_2249: "oc_sub oc_b30 2249"
  by (oc_eval oc_c30_2249)

lemma oc_c30_2250: "oc_sub oc_b30 2250"
  by (oc_eval oc_c30_2250)

lemma oc_c30_2251: "oc_sub oc_b30 2251"
  by (oc_eval oc_c30_2251)

lemma oc_c30_2252: "oc_sub oc_b30 2252"
  by (oc_eval oc_c30_2252)

lemma oc_c30_2253: "oc_sub oc_b30 2253"
  by (oc_eval oc_c30_2253)

lemma oc_c30_2254: "oc_sub oc_b30 2254"
  by (oc_eval oc_c30_2254)

lemma oc_c30_2255: "oc_sub oc_b30 2255"
  by (oc_eval oc_c30_2255)

lemma upt_c30_140: "[2240..<2256] = [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]"
  by (simp add: upt_rec)

lemma sec_c30_140: "\<forall>j\<in>{16 * 140..<16 * 140 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 140..<16 * 140 + 16}"
  then have "j \<in> set [2240..<2256]" unfolding set_upt by simp
  then have "j \<in> set [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]" unfolding upt_c30_140 .
  then show "oc_sub oc_b30 j" using oc_c30_2240 oc_c30_2241 oc_c30_2242 oc_c30_2243 oc_c30_2244 oc_c30_2245 oc_c30_2246 oc_c30_2247 oc_c30_2248 oc_c30_2249 oc_c30_2250 oc_c30_2251 oc_c30_2252 oc_c30_2253 oc_c30_2254 oc_c30_2255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
