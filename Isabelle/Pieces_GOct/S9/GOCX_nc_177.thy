theory GOCX_nc_177
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2832: "goc_sub None 2832"
  by (goc_eval goc_nc_2832)

lemma goc_nc_2833: "goc_sub None 2833"
  by (goc_eval goc_nc_2833)

lemma goc_nc_2834: "goc_sub None 2834"
  by (goc_eval goc_nc_2834)

lemma goc_nc_2835: "goc_sub None 2835"
  by (goc_eval goc_nc_2835)

lemma goc_nc_2836: "goc_sub None 2836"
  by (goc_eval goc_nc_2836)

lemma goc_nc_2837: "goc_sub None 2837"
  by (goc_eval goc_nc_2837)

lemma goc_nc_2838: "goc_sub None 2838"
  by (goc_eval goc_nc_2838)

lemma goc_nc_2839: "goc_sub None 2839"
  by (goc_eval goc_nc_2839)

lemma goc_nc_2840: "goc_sub None 2840"
  by (goc_eval goc_nc_2840)

lemma goc_nc_2841: "goc_sub None 2841"
  by (goc_eval goc_nc_2841)

lemma goc_nc_2842: "goc_sub None 2842"
  by (goc_eval goc_nc_2842)

lemma goc_nc_2843: "goc_sub None 2843"
  by (goc_eval goc_nc_2843)

lemma goc_nc_2844: "goc_sub None 2844"
  by (goc_eval goc_nc_2844)

lemma goc_nc_2845: "goc_sub None 2845"
  by (goc_eval goc_nc_2845)

lemma goc_nc_2846: "goc_sub None 2846"
  by (goc_eval goc_nc_2846)

lemma goc_nc_2847: "goc_sub None 2847"
  by (goc_eval goc_nc_2847)

lemma gupt_nc_177: "[2832..<2848] = [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]"
  by (simp add: upt_rec)

lemma gsec_nc_177: "\<forall>j\<in>{16 * 177..<16 * 177 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 177..<16 * 177 + 16}"
  then have "j \<in> set [2832..<2848]" unfolding set_upt by simp
  then have "j \<in> set [2832, 2833, 2834, 2835, 2836, 2837, 2838, 2839, 2840, 2841, 2842, 2843, 2844, 2845, 2846, 2847]" unfolding gupt_nc_177 .
  then show "goc_sub None j" using goc_nc_2832 goc_nc_2833 goc_nc_2834 goc_nc_2835 goc_nc_2836 goc_nc_2837 goc_nc_2838 goc_nc_2839 goc_nc_2840 goc_nc_2841 goc_nc_2842 goc_nc_2843 goc_nc_2844 goc_nc_2845 goc_nc_2846 goc_nc_2847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
