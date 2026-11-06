theory OCX_nc_174
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2784: "oc_sub None 2784"
  by (oc_eval oc_nc_2784)

lemma oc_nc_2785: "oc_sub None 2785"
  by (oc_eval oc_nc_2785)

lemma oc_nc_2786: "oc_sub None 2786"
  by (oc_eval oc_nc_2786)

lemma oc_nc_2787: "oc_sub None 2787"
  by (oc_eval oc_nc_2787)

lemma oc_nc_2788: "oc_sub None 2788"
  by (oc_eval oc_nc_2788)

lemma oc_nc_2789: "oc_sub None 2789"
  by (oc_eval oc_nc_2789)

lemma oc_nc_2790: "oc_sub None 2790"
  by (oc_eval oc_nc_2790)

lemma oc_nc_2791: "oc_sub None 2791"
  by (oc_eval oc_nc_2791)

lemma oc_nc_2792: "oc_sub None 2792"
  by (oc_eval oc_nc_2792)

lemma oc_nc_2793: "oc_sub None 2793"
  by (oc_eval oc_nc_2793)

lemma oc_nc_2794: "oc_sub None 2794"
  by (oc_eval oc_nc_2794)

lemma oc_nc_2795: "oc_sub None 2795"
  by (oc_eval oc_nc_2795)

lemma oc_nc_2796: "oc_sub None 2796"
  by (oc_eval oc_nc_2796)

lemma oc_nc_2797: "oc_sub None 2797"
  by (oc_eval oc_nc_2797)

lemma oc_nc_2798: "oc_sub None 2798"
  by (oc_eval oc_nc_2798)

lemma oc_nc_2799: "oc_sub None 2799"
  by (oc_eval oc_nc_2799)

lemma upt_nc_174: "[2784..<2800] = [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]"
  by (simp add: upt_rec)

lemma sec_nc_174: "\<forall>j\<in>{16 * 174..<16 * 174 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 174..<16 * 174 + 16}"
  then have "j \<in> set [2784..<2800]" unfolding set_upt by simp
  then have "j \<in> set [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]" unfolding upt_nc_174 .
  then show "oc_sub None j" using oc_nc_2784 oc_nc_2785 oc_nc_2786 oc_nc_2787 oc_nc_2788 oc_nc_2789 oc_nc_2790 oc_nc_2791 oc_nc_2792 oc_nc_2793 oc_nc_2794 oc_nc_2795 oc_nc_2796 oc_nc_2797 oc_nc_2798 oc_nc_2799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
