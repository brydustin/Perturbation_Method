theory OCX_c30_042
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0672: "oc_sub oc_b30 672"
  by (oc_eval oc_c30_0672)

lemma oc_c30_0673: "oc_sub oc_b30 673"
  by (oc_eval oc_c30_0673)

lemma oc_c30_0674: "oc_sub oc_b30 674"
  by (oc_eval oc_c30_0674)

lemma oc_c30_0675: "oc_sub oc_b30 675"
  by (oc_eval oc_c30_0675)

lemma oc_c30_0676: "oc_sub oc_b30 676"
  by (oc_eval oc_c30_0676)

lemma oc_c30_0677: "oc_sub oc_b30 677"
  by (oc_eval oc_c30_0677)

lemma oc_c30_0678: "oc_sub oc_b30 678"
  by (oc_eval oc_c30_0678)

lemma oc_c30_0679: "oc_sub oc_b30 679"
  by (oc_eval oc_c30_0679)

lemma oc_c30_0680: "oc_sub oc_b30 680"
  by (oc_eval oc_c30_0680)

lemma oc_c30_0681: "oc_sub oc_b30 681"
  by (oc_eval oc_c30_0681)

lemma oc_c30_0682: "oc_sub oc_b30 682"
  by (oc_eval oc_c30_0682)

lemma oc_c30_0683: "oc_sub oc_b30 683"
  by (oc_eval oc_c30_0683)

lemma oc_c30_0684: "oc_sub oc_b30 684"
  by (oc_eval oc_c30_0684)

lemma oc_c30_0685: "oc_sub oc_b30 685"
  by (oc_eval oc_c30_0685)

lemma oc_c30_0686: "oc_sub oc_b30 686"
  by (oc_eval oc_c30_0686)

lemma oc_c30_0687: "oc_sub oc_b30 687"
  by (oc_eval oc_c30_0687)

lemma upt_c30_042: "[672..<688] = [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]"
  by (simp add: upt_rec)

lemma sec_c30_042: "\<forall>j\<in>{16 * 42..<16 * 42 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 42..<16 * 42 + 16}"
  then have "j \<in> set [672..<688]" unfolding set_upt by simp
  then have "j \<in> set [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687]" unfolding upt_c30_042 .
  then show "oc_sub oc_b30 j" using oc_c30_0672 oc_c30_0673 oc_c30_0674 oc_c30_0675 oc_c30_0676 oc_c30_0677 oc_c30_0678 oc_c30_0679 oc_c30_0680 oc_c30_0681 oc_c30_0682 oc_c30_0683 oc_c30_0684 oc_c30_0685 oc_c30_0686 oc_c30_0687
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
