theory OCX_c30_174
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2784: "oc_sub oc_b30 2784"
  by (oc_eval oc_c30_2784)

lemma oc_c30_2785: "oc_sub oc_b30 2785"
  by (oc_eval oc_c30_2785)

lemma oc_c30_2786: "oc_sub oc_b30 2786"
  by (oc_eval oc_c30_2786)

lemma oc_c30_2787: "oc_sub oc_b30 2787"
  by (oc_eval oc_c30_2787)

lemma oc_c30_2788: "oc_sub oc_b30 2788"
  by (oc_eval oc_c30_2788)

lemma oc_c30_2789: "oc_sub oc_b30 2789"
  by (oc_eval oc_c30_2789)

lemma oc_c30_2790: "oc_sub oc_b30 2790"
  by (oc_eval oc_c30_2790)

lemma oc_c30_2791: "oc_sub oc_b30 2791"
  by (oc_eval oc_c30_2791)

lemma oc_c30_2792: "oc_sub oc_b30 2792"
  by (oc_eval oc_c30_2792)

lemma oc_c30_2793: "oc_sub oc_b30 2793"
  by (oc_eval oc_c30_2793)

lemma oc_c30_2794: "oc_sub oc_b30 2794"
  by (oc_eval oc_c30_2794)

lemma oc_c30_2795: "oc_sub oc_b30 2795"
  by (oc_eval oc_c30_2795)

lemma oc_c30_2796: "oc_sub oc_b30 2796"
  by (oc_eval oc_c30_2796)

lemma oc_c30_2797: "oc_sub oc_b30 2797"
  by (oc_eval oc_c30_2797)

lemma oc_c30_2798: "oc_sub oc_b30 2798"
  by (oc_eval oc_c30_2798)

lemma oc_c30_2799: "oc_sub oc_b30 2799"
  by (oc_eval oc_c30_2799)

lemma upt_c30_174: "[2784..<2800] = [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]"
  by (simp add: upt_rec)

lemma sec_c30_174: "\<forall>j\<in>{16 * 174..<16 * 174 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 174..<16 * 174 + 16}"
  then have "j \<in> set [2784..<2800]" unfolding set_upt by simp
  then have "j \<in> set [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]" unfolding upt_c30_174 .
  then show "oc_sub oc_b30 j" using oc_c30_2784 oc_c30_2785 oc_c30_2786 oc_c30_2787 oc_c30_2788 oc_c30_2789 oc_c30_2790 oc_c30_2791 oc_c30_2792 oc_c30_2793 oc_c30_2794 oc_c30_2795 oc_c30_2796 oc_c30_2797 oc_c30_2798 oc_c30_2799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
