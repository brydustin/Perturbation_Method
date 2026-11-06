theory OCX_nc_000
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0000: "oc_sub None 0"
  by (oc_eval oc_nc_0000)

lemma oc_nc_0001: "oc_sub None 1"
  by (oc_eval oc_nc_0001)

lemma oc_nc_0002: "oc_sub None 2"
  by (oc_eval oc_nc_0002)

lemma oc_nc_0003: "oc_sub None 3"
  by (oc_eval oc_nc_0003)

lemma oc_nc_0004: "oc_sub None 4"
  by (oc_eval oc_nc_0004)

lemma oc_nc_0005: "oc_sub None 5"
  by (oc_eval oc_nc_0005)

lemma oc_nc_0006: "oc_sub None 6"
  by (oc_eval oc_nc_0006)

lemma oc_nc_0007: "oc_sub None 7"
  by (oc_eval oc_nc_0007)

lemma oc_nc_0008: "oc_sub None 8"
  by (oc_eval oc_nc_0008)

lemma oc_nc_0009: "oc_sub None 9"
  by (oc_eval oc_nc_0009)

lemma oc_nc_0010: "oc_sub None 10"
  by (oc_eval oc_nc_0010)

lemma oc_nc_0011: "oc_sub None 11"
  by (oc_eval oc_nc_0011)

lemma oc_nc_0012: "oc_sub None 12"
  by (oc_eval oc_nc_0012)

lemma oc_nc_0013: "oc_sub None 13"
  by (oc_eval oc_nc_0013)

lemma oc_nc_0014: "oc_sub None 14"
  by (oc_eval oc_nc_0014)

lemma oc_nc_0015: "oc_sub None 15"
  by (oc_eval oc_nc_0015)

lemma upt_nc_000: "[0..<16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
  by (simp add: upt_rec)

lemma sec_nc_000: "\<forall>j\<in>{16 * 0..<16 * 0 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 0..<16 * 0 + 16}"
  then have "j \<in> set [0..<16]" unfolding set_upt by simp
  then have "j \<in> set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]" unfolding upt_nc_000 .
  then show "oc_sub None j" using oc_nc_0000 oc_nc_0001 oc_nc_0002 oc_nc_0003 oc_nc_0004 oc_nc_0005 oc_nc_0006 oc_nc_0007 oc_nc_0008 oc_nc_0009 oc_nc_0010 oc_nc_0011 oc_nc_0012 oc_nc_0013 oc_nc_0014 oc_nc_0015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
