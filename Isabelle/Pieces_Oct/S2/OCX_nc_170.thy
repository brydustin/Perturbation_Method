theory OCX_nc_170
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2720: "oc_sub None 2720"
  by (oc_eval oc_nc_2720)

lemma oc_nc_2721: "oc_sub None 2721"
  by (oc_eval oc_nc_2721)

lemma oc_nc_2722: "oc_sub None 2722"
  by (oc_eval oc_nc_2722)

lemma oc_nc_2723: "oc_sub None 2723"
  by (oc_eval oc_nc_2723)

lemma oc_nc_2724: "oc_sub None 2724"
  by (oc_eval oc_nc_2724)

lemma oc_nc_2725: "oc_sub None 2725"
  by (oc_eval oc_nc_2725)

lemma oc_nc_2726: "oc_sub None 2726"
  by (oc_eval oc_nc_2726)

lemma oc_nc_2727: "oc_sub None 2727"
  by (oc_eval oc_nc_2727)

lemma oc_nc_2728: "oc_sub None 2728"
  by (oc_eval oc_nc_2728)

lemma oc_nc_2729: "oc_sub None 2729"
  by (oc_eval oc_nc_2729)

lemma oc_nc_2730: "oc_sub None 2730"
  by (oc_eval oc_nc_2730)

lemma oc_nc_2731: "oc_sub None 2731"
  by (oc_eval oc_nc_2731)

lemma oc_nc_2732: "oc_sub None 2732"
  by (oc_eval oc_nc_2732)

lemma oc_nc_2733: "oc_sub None 2733"
  by (oc_eval oc_nc_2733)

lemma oc_nc_2734: "oc_sub None 2734"
  by (oc_eval oc_nc_2734)

lemma oc_nc_2735: "oc_sub None 2735"
  by (oc_eval oc_nc_2735)

lemma upt_nc_170: "[2720..<2736] = [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]"
  by (simp add: upt_rec)

lemma sec_nc_170: "\<forall>j\<in>{16 * 170..<16 * 170 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 170..<16 * 170 + 16}"
  then have "j \<in> set [2720..<2736]" unfolding set_upt by simp
  then have "j \<in> set [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]" unfolding upt_nc_170 .
  then show "oc_sub None j" using oc_nc_2720 oc_nc_2721 oc_nc_2722 oc_nc_2723 oc_nc_2724 oc_nc_2725 oc_nc_2726 oc_nc_2727 oc_nc_2728 oc_nc_2729 oc_nc_2730 oc_nc_2731 oc_nc_2732 oc_nc_2733 oc_nc_2734 oc_nc_2735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
