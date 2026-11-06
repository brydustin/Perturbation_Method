theory GOCX_nc_052
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0832: "goc_sub None 832"
  by (goc_eval goc_nc_0832)

lemma goc_nc_0833: "goc_sub None 833"
  by (goc_eval goc_nc_0833)

lemma goc_nc_0834: "goc_sub None 834"
  by (goc_eval goc_nc_0834)

lemma goc_nc_0835: "goc_sub None 835"
  by (goc_eval goc_nc_0835)

lemma goc_nc_0836: "goc_sub None 836"
  by (goc_eval goc_nc_0836)

lemma goc_nc_0837: "goc_sub None 837"
  by (goc_eval goc_nc_0837)

lemma goc_nc_0838: "goc_sub None 838"
  by (goc_eval goc_nc_0838)

lemma goc_nc_0839: "goc_sub None 839"
  by (goc_eval goc_nc_0839)

lemma goc_nc_0840: "goc_sub None 840"
  by (goc_eval goc_nc_0840)

lemma goc_nc_0841: "goc_sub None 841"
  by (goc_eval goc_nc_0841)

lemma goc_nc_0842: "goc_sub None 842"
  by (goc_eval goc_nc_0842)

lemma goc_nc_0843: "goc_sub None 843"
  by (goc_eval goc_nc_0843)

lemma goc_nc_0844: "goc_sub None 844"
  by (goc_eval goc_nc_0844)

lemma goc_nc_0845: "goc_sub None 845"
  by (goc_eval goc_nc_0845)

lemma goc_nc_0846: "goc_sub None 846"
  by (goc_eval goc_nc_0846)

lemma goc_nc_0847: "goc_sub None 847"
  by (goc_eval goc_nc_0847)

lemma gupt_nc_052: "[832..<848] = [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]"
  by (simp add: upt_rec)

lemma gsec_nc_052: "\<forall>j\<in>{16 * 52..<16 * 52 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 52..<16 * 52 + 16}"
  then have "j \<in> set [832..<848]" unfolding set_upt by simp
  then have "j \<in> set [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]" unfolding gupt_nc_052 .
  then show "goc_sub None j" using goc_nc_0832 goc_nc_0833 goc_nc_0834 goc_nc_0835 goc_nc_0836 goc_nc_0837 goc_nc_0838 goc_nc_0839 goc_nc_0840 goc_nc_0841 goc_nc_0842 goc_nc_0843 goc_nc_0844 goc_nc_0845 goc_nc_0846 goc_nc_0847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
