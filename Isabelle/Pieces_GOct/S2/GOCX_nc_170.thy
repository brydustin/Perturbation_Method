theory GOCX_nc_170
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2720: "goc_sub None 2720"
  by (goc_eval goc_nc_2720)

lemma goc_nc_2721: "goc_sub None 2721"
  by (goc_eval goc_nc_2721)

lemma goc_nc_2722: "goc_sub None 2722"
  by (goc_eval goc_nc_2722)

lemma goc_nc_2723: "goc_sub None 2723"
  by (goc_eval goc_nc_2723)

lemma goc_nc_2724: "goc_sub None 2724"
  by (goc_eval goc_nc_2724)

lemma goc_nc_2725: "goc_sub None 2725"
  by (goc_eval goc_nc_2725)

lemma goc_nc_2726: "goc_sub None 2726"
  by (goc_eval goc_nc_2726)

lemma goc_nc_2727: "goc_sub None 2727"
  by (goc_eval goc_nc_2727)

lemma goc_nc_2728: "goc_sub None 2728"
  by (goc_eval goc_nc_2728)

lemma goc_nc_2729: "goc_sub None 2729"
  by (goc_eval goc_nc_2729)

lemma goc_nc_2730: "goc_sub None 2730"
  by (goc_eval goc_nc_2730)

lemma goc_nc_2731: "goc_sub None 2731"
  by (goc_eval goc_nc_2731)

lemma goc_nc_2732: "goc_sub None 2732"
  by (goc_eval goc_nc_2732)

lemma goc_nc_2733: "goc_sub None 2733"
  by (goc_eval goc_nc_2733)

lemma goc_nc_2734: "goc_sub None 2734"
  by (goc_eval goc_nc_2734)

lemma goc_nc_2735: "goc_sub None 2735"
  by (goc_eval goc_nc_2735)

lemma gupt_nc_170: "[2720..<2736] = [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]"
  by (simp add: upt_rec)

lemma gsec_nc_170: "\<forall>j\<in>{16 * 170..<16 * 170 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 170..<16 * 170 + 16}"
  then have "j \<in> set [2720..<2736]" unfolding set_upt by simp
  then have "j \<in> set [2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735]" unfolding gupt_nc_170 .
  then show "goc_sub None j" using goc_nc_2720 goc_nc_2721 goc_nc_2722 goc_nc_2723 goc_nc_2724 goc_nc_2725 goc_nc_2726 goc_nc_2727 goc_nc_2728 goc_nc_2729 goc_nc_2730 goc_nc_2731 goc_nc_2732 goc_nc_2733 goc_nc_2734 goc_nc_2735
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
