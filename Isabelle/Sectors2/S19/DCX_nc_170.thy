theory DCX_nc_170
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2720: "dc_sub None 2720"
  by (dc_eval dc_nc_2720)

lemma dc_nc_2721: "dc_sub None 2721"
  by (dc_eval dc_nc_2721)

lemma dc_nc_2722: "dc_sub None 2722"
  by (dc_eval dc_nc_2722)

lemma dc_nc_2723: "dc_sub None 2723"
  by (dc_eval dc_nc_2723)

lemma dc_nc_2724: "dc_sub None 2724"
  by (dc_eval dc_nc_2724)

lemma dc_nc_2725: "dc_sub None 2725"
  by (dc_eval dc_nc_2725)

lemma dc_nc_2726: "dc_sub None 2726"
  by (dc_eval dc_nc_2726)

lemma dc_nc_2727: "dc_sub None 2727"
  by (dc_eval dc_nc_2727)

lemma dc_nc_2728: "dc_sub None 2728"
  by (dc_eval dc_nc_2728)

lemma dc_nc_2729: "dc_sub None 2729"
  by (dc_eval dc_nc_2729)

lemma dc_nc_2730: "dc_sub None 2730"
  by (dc_eval dc_nc_2730)

lemma dc_nc_2731: "dc_sub None 2731"
  by (dc_eval dc_nc_2731)

lemma dc_nc_2732: "dc_sub None 2732"
  by (dc_eval dc_nc_2732)

lemma dc_nc_2733: "dc_sub None 2733"
  by (dc_eval dc_nc_2733)

lemma dc_nc_2734: "dc_sub None 2734"
  by (dc_eval dc_nc_2734)

lemma dc_nc_2735: "dc_sub None 2735"
  by (dc_eval dc_nc_2735)

lemma upt_nc_170: "[2720..<2736] = [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]"
  by (simp add: upt_rec)

lemma sec_nc_170: "\<forall>j\<in>{16 * 170..<16 * 170 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 170..<16 * 170 + 16}"
  then have "j \<in> set [2720..<2736]" unfolding set_upt by simp
  then have "j \<in> set [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]" unfolding upt_nc_170 .
  then show "dc_sub None j" using dc_nc_2720 dc_nc_2721 dc_nc_2722 dc_nc_2723 dc_nc_2724 dc_nc_2725 dc_nc_2726 dc_nc_2727 dc_nc_2728 dc_nc_2729 dc_nc_2730 dc_nc_2731 dc_nc_2732 dc_nc_2733 dc_nc_2734 dc_nc_2735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
