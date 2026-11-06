theory OCX_nc_052
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0832: "oc_sub None 832"
  by (oc_eval oc_nc_0832)

lemma oc_nc_0833: "oc_sub None 833"
  by (oc_eval oc_nc_0833)

lemma oc_nc_0834: "oc_sub None 834"
  by (oc_eval oc_nc_0834)

lemma oc_nc_0835: "oc_sub None 835"
  by (oc_eval oc_nc_0835)

lemma oc_nc_0836: "oc_sub None 836"
  by (oc_eval oc_nc_0836)

lemma oc_nc_0837: "oc_sub None 837"
  by (oc_eval oc_nc_0837)

lemma oc_nc_0838: "oc_sub None 838"
  by (oc_eval oc_nc_0838)

lemma oc_nc_0839: "oc_sub None 839"
  by (oc_eval oc_nc_0839)

lemma oc_nc_0840: "oc_sub None 840"
  by (oc_eval oc_nc_0840)

lemma oc_nc_0841: "oc_sub None 841"
  by (oc_eval oc_nc_0841)

lemma oc_nc_0842: "oc_sub None 842"
  by (oc_eval oc_nc_0842)

lemma oc_nc_0843: "oc_sub None 843"
  by (oc_eval oc_nc_0843)

lemma oc_nc_0844: "oc_sub None 844"
  by (oc_eval oc_nc_0844)

lemma oc_nc_0845: "oc_sub None 845"
  by (oc_eval oc_nc_0845)

lemma oc_nc_0846: "oc_sub None 846"
  by (oc_eval oc_nc_0846)

lemma oc_nc_0847: "oc_sub None 847"
  by (oc_eval oc_nc_0847)

lemma upt_nc_052: "[832..<848] = [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]"
  by (simp add: upt_rec)

lemma sec_nc_052: "\<forall>j\<in>{16 * 52..<16 * 52 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 52..<16 * 52 + 16}"
  then have "j \<in> set [832..<848]" unfolding set_upt by simp
  then have "j \<in> set [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847]" unfolding upt_nc_052 .
  then show "oc_sub None j" using oc_nc_0832 oc_nc_0833 oc_nc_0834 oc_nc_0835 oc_nc_0836 oc_nc_0837 oc_nc_0838 oc_nc_0839 oc_nc_0840 oc_nc_0841 oc_nc_0842 oc_nc_0843 oc_nc_0844 oc_nc_0845 oc_nc_0846 oc_nc_0847
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
