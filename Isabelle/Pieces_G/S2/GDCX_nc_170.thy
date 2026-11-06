theory GDCX_nc_170
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2720: "gdc_sub None 2720"
  by (gdc_eval gdc_nc_2720)

lemma gdc_nc_2721: "gdc_sub None 2721"
  by (gdc_eval gdc_nc_2721)

lemma gdc_nc_2722: "gdc_sub None 2722"
  by (gdc_eval gdc_nc_2722)

lemma gdc_nc_2723: "gdc_sub None 2723"
  by (gdc_eval gdc_nc_2723)

lemma gdc_nc_2724: "gdc_sub None 2724"
  by (gdc_eval gdc_nc_2724)

lemma gdc_nc_2725: "gdc_sub None 2725"
  by (gdc_eval gdc_nc_2725)

lemma gdc_nc_2726: "gdc_sub None 2726"
  by (gdc_eval gdc_nc_2726)

lemma gdc_nc_2727: "gdc_sub None 2727"
  by (gdc_eval gdc_nc_2727)

lemma gdc_nc_2728: "gdc_sub None 2728"
  by (gdc_eval gdc_nc_2728)

lemma gdc_nc_2729: "gdc_sub None 2729"
  by (gdc_eval gdc_nc_2729)

lemma gdc_nc_2730: "gdc_sub None 2730"
  by (gdc_eval gdc_nc_2730)

lemma gdc_nc_2731: "gdc_sub None 2731"
  by (gdc_eval gdc_nc_2731)

lemma gdc_nc_2732: "gdc_sub None 2732"
  by (gdc_eval gdc_nc_2732)

lemma gdc_nc_2733: "gdc_sub None 2733"
  by (gdc_eval gdc_nc_2733)

lemma gdc_nc_2734: "gdc_sub None 2734"
  by (gdc_eval gdc_nc_2734)

lemma gdc_nc_2735: "gdc_sub None 2735"
  by (gdc_eval gdc_nc_2735)

lemma gupt_nc_170: "[2720..<2736] = [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]"
  by (simp add: upt_rec)

lemma gsec_nc_170: "\<forall>j\<in>{16 * 170..<16 * 170 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 170..<16 * 170 + 16}"
  then have "j \<in> set [2720..<2736]" unfolding set_upt by simp
  then have "j \<in> set [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]" unfolding gupt_nc_170 .
  then show "gdc_sub None j" using gdc_nc_2720 gdc_nc_2721 gdc_nc_2722 gdc_nc_2723 gdc_nc_2724 gdc_nc_2725 gdc_nc_2726 gdc_nc_2727 gdc_nc_2728 gdc_nc_2729 gdc_nc_2730 gdc_nc_2731 gdc_nc_2732 gdc_nc_2733 gdc_nc_2734 gdc_nc_2735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
