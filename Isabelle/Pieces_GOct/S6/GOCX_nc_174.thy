theory GOCX_nc_174
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2784: "goc_sub None 2784"
  by (goc_eval goc_nc_2784)

lemma goc_nc_2785: "goc_sub None 2785"
  by (goc_eval goc_nc_2785)

lemma goc_nc_2786: "goc_sub None 2786"
  by (goc_eval goc_nc_2786)

lemma goc_nc_2787: "goc_sub None 2787"
  by (goc_eval goc_nc_2787)

lemma goc_nc_2788: "goc_sub None 2788"
  by (goc_eval goc_nc_2788)

lemma goc_nc_2789: "goc_sub None 2789"
  by (goc_eval goc_nc_2789)

lemma goc_nc_2790: "goc_sub None 2790"
  by (goc_eval goc_nc_2790)

lemma goc_nc_2791: "goc_sub None 2791"
  by (goc_eval goc_nc_2791)

lemma goc_nc_2792: "goc_sub None 2792"
  by (goc_eval goc_nc_2792)

lemma goc_nc_2793: "goc_sub None 2793"
  by (goc_eval goc_nc_2793)

lemma goc_nc_2794: "goc_sub None 2794"
  by (goc_eval goc_nc_2794)

lemma goc_nc_2795: "goc_sub None 2795"
  by (goc_eval goc_nc_2795)

lemma goc_nc_2796: "goc_sub None 2796"
  by (goc_eval goc_nc_2796)

lemma goc_nc_2797: "goc_sub None 2797"
  by (goc_eval goc_nc_2797)

lemma goc_nc_2798: "goc_sub None 2798"
  by (goc_eval goc_nc_2798)

lemma goc_nc_2799: "goc_sub None 2799"
  by (goc_eval goc_nc_2799)

lemma gupt_nc_174: "[2784..<2800] = [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]"
  by (simp add: upt_rec)

lemma gsec_nc_174: "\<forall>j\<in>{16 * 174..<16 * 174 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 174..<16 * 174 + 16}"
  then have "j \<in> set [2784..<2800]" unfolding set_upt by simp
  then have "j \<in> set [2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799]" unfolding gupt_nc_174 .
  then show "goc_sub None j" using goc_nc_2784 goc_nc_2785 goc_nc_2786 goc_nc_2787 goc_nc_2788 goc_nc_2789 goc_nc_2790 goc_nc_2791 goc_nc_2792 goc_nc_2793 goc_nc_2794 goc_nc_2795 goc_nc_2796 goc_nc_2797 goc_nc_2798 goc_nc_2799
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
