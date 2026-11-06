theory GOCX_nc_042
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0672: "goc_sub None 672"
  by (goc_eval goc_nc_0672)

lemma goc_nc_0673: "goc_sub None 673"
  by (goc_eval goc_nc_0673)

lemma goc_nc_0674: "goc_sub None 674"
  by (goc_eval goc_nc_0674)

lemma goc_nc_0675: "goc_sub None 675"
  by (goc_eval goc_nc_0675)

lemma goc_nc_0676: "goc_sub None 676"
  by (goc_eval goc_nc_0676)

lemma goc_nc_0677: "goc_sub None 677"
  by (goc_eval goc_nc_0677)

lemma goc_nc_0678: "goc_sub None 678"
  by (goc_eval goc_nc_0678)

lemma goc_nc_0679: "goc_sub None 679"
  by (goc_eval goc_nc_0679)

lemma goc_nc_0680: "goc_sub None 680"
  by (goc_eval goc_nc_0680)

lemma goc_nc_0681: "goc_sub None 681"
  by (goc_eval goc_nc_0681)

lemma goc_nc_0682: "goc_sub None 682"
  by (goc_eval goc_nc_0682)

lemma goc_nc_0683: "goc_sub None 683"
  by (goc_eval goc_nc_0683)

lemma goc_nc_0684: "goc_sub None 684"
  by (goc_eval goc_nc_0684)

lemma goc_nc_0685: "goc_sub None 685"
  by (goc_eval goc_nc_0685)

lemma goc_nc_0686: "goc_sub None 686"
  by (goc_eval goc_nc_0686)

lemma goc_nc_0687: "goc_sub None 687"
  by (goc_eval goc_nc_0687)

lemma gupt_nc_042: "[672..<688] = [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]"
  by (simp add: upt_rec)

lemma gsec_nc_042: "\<forall>j\<in>{16 * 42..<16 * 42 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 42..<16 * 42 + 16}"
  then have "j \<in> set [672..<688]" unfolding set_upt by simp
  then have "j \<in> set [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]" unfolding gupt_nc_042 .
  then show "goc_sub None j" using goc_nc_0672 goc_nc_0673 goc_nc_0674 goc_nc_0675 goc_nc_0676 goc_nc_0677 goc_nc_0678 goc_nc_0679 goc_nc_0680 goc_nc_0681 goc_nc_0682 goc_nc_0683 goc_nc_0684 goc_nc_0685 goc_nc_0686 goc_nc_0687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
