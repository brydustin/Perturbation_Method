theory DCX_c30_170
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2720: "dc_sub dc_b30 2720"
  by (dc_eval dc_c30_2720)

lemma dc_c30_2721: "dc_sub dc_b30 2721"
  by (dc_eval dc_c30_2721)

lemma dc_c30_2722: "dc_sub dc_b30 2722"
  by (dc_eval dc_c30_2722)

lemma dc_c30_2723: "dc_sub dc_b30 2723"
  by (dc_eval dc_c30_2723)

lemma dc_c30_2724: "dc_sub dc_b30 2724"
  by (dc_eval dc_c30_2724)

lemma dc_c30_2725: "dc_sub dc_b30 2725"
  by (dc_eval dc_c30_2725)

lemma dc_c30_2726: "dc_sub dc_b30 2726"
  by (dc_eval dc_c30_2726)

lemma dc_c30_2727: "dc_sub dc_b30 2727"
  by (dc_eval dc_c30_2727)

lemma dc_c30_2728: "dc_sub dc_b30 2728"
  by (dc_eval dc_c30_2728)

lemma dc_c30_2729: "dc_sub dc_b30 2729"
  by (dc_eval dc_c30_2729)

lemma dc_c30_2730: "dc_sub dc_b30 2730"
  by (dc_eval dc_c30_2730)

lemma dc_c30_2731: "dc_sub dc_b30 2731"
  by (dc_eval dc_c30_2731)

lemma dc_c30_2732: "dc_sub dc_b30 2732"
  by (dc_eval dc_c30_2732)

lemma dc_c30_2733: "dc_sub dc_b30 2733"
  by (dc_eval dc_c30_2733)

lemma dc_c30_2734: "dc_sub dc_b30 2734"
  by (dc_eval dc_c30_2734)

lemma dc_c30_2735: "dc_sub dc_b30 2735"
  by (dc_eval dc_c30_2735)

lemma upt_c30_170: "[2720..<2736] = [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]"
  by (simp add: upt_rec)

lemma sec_c30_170: "\<forall>j\<in>{16 * 170..<16 * 170 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 170..<16 * 170 + 16}"
  then have "j \<in> set [2720..<2736]" unfolding set_upt by simp
  then have "j \<in> set [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]" unfolding upt_c30_170 .
  then show "dc_sub dc_b30 j" using dc_c30_2720 dc_c30_2721 dc_c30_2722 dc_c30_2723 dc_c30_2724 dc_c30_2725 dc_c30_2726 dc_c30_2727 dc_c30_2728 dc_c30_2729 dc_c30_2730 dc_c30_2731 dc_c30_2732 dc_c30_2733 dc_c30_2734 dc_c30_2735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
