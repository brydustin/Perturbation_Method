theory GDCX_nc_042
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0672: "gdc_sub None 672"
  by (gdc_eval gdc_nc_0672)

lemma gdc_nc_0673: "gdc_sub None 673"
  by (gdc_eval gdc_nc_0673)

lemma gdc_nc_0674: "gdc_sub None 674"
  by (gdc_eval gdc_nc_0674)

lemma gdc_nc_0675: "gdc_sub None 675"
  by (gdc_eval gdc_nc_0675)

lemma gdc_nc_0676: "gdc_sub None 676"
  by (gdc_eval gdc_nc_0676)

lemma gdc_nc_0677: "gdc_sub None 677"
  by (gdc_eval gdc_nc_0677)

lemma gdc_nc_0678: "gdc_sub None 678"
  by (gdc_eval gdc_nc_0678)

lemma gdc_nc_0679: "gdc_sub None 679"
  by (gdc_eval gdc_nc_0679)

lemma gdc_nc_0680: "gdc_sub None 680"
  by (gdc_eval gdc_nc_0680)

lemma gdc_nc_0681: "gdc_sub None 681"
  by (gdc_eval gdc_nc_0681)

lemma gdc_nc_0682: "gdc_sub None 682"
  by (gdc_eval gdc_nc_0682)

lemma gdc_nc_0683: "gdc_sub None 683"
  by (gdc_eval gdc_nc_0683)

lemma gdc_nc_0684: "gdc_sub None 684"
  by (gdc_eval gdc_nc_0684)

lemma gdc_nc_0685: "gdc_sub None 685"
  by (gdc_eval gdc_nc_0685)

lemma gdc_nc_0686: "gdc_sub None 686"
  by (gdc_eval gdc_nc_0686)

lemma gdc_nc_0687: "gdc_sub None 687"
  by (gdc_eval gdc_nc_0687)

lemma gupt_nc_042: "[672..<688] = [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]"
  by (simp add: upt_rec)

lemma gsec_nc_042: "\<forall>j\<in>{16 * 42..<16 * 42 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 42..<16 * 42 + 16}"
  then have "j \<in> set [672..<688]" unfolding set_upt by simp
  then have "j \<in> set [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]" unfolding gupt_nc_042 .
  then show "gdc_sub None j" using gdc_nc_0672 gdc_nc_0673 gdc_nc_0674 gdc_nc_0675 gdc_nc_0676 gdc_nc_0677 gdc_nc_0678 gdc_nc_0679 gdc_nc_0680 gdc_nc_0681 gdc_nc_0682 gdc_nc_0683 gdc_nc_0684 gdc_nc_0685 gdc_nc_0686 gdc_nc_0687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
