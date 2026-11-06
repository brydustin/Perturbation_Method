theory OCX_c30_000
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0000: "oc_sub oc_b30 0"
  by (oc_eval oc_c30_0000)

lemma oc_c30_0001: "oc_sub oc_b30 1"
  by (oc_eval oc_c30_0001)

lemma oc_c30_0002: "oc_sub oc_b30 2"
  by (oc_eval oc_c30_0002)

lemma oc_c30_0003: "oc_sub oc_b30 3"
  by (oc_eval oc_c30_0003)

lemma oc_c30_0004: "oc_sub oc_b30 4"
  by (oc_eval oc_c30_0004)

lemma oc_c30_0005: "oc_sub oc_b30 5"
  by (oc_eval oc_c30_0005)

lemma oc_c30_0006: "oc_sub oc_b30 6"
  by (oc_eval oc_c30_0006)

lemma oc_c30_0007: "oc_sub oc_b30 7"
  by (oc_eval oc_c30_0007)

lemma oc_c30_0008: "oc_sub oc_b30 8"
  by (oc_eval oc_c30_0008)

lemma oc_c30_0009: "oc_sub oc_b30 9"
  by (oc_eval oc_c30_0009)

lemma oc_c30_0010: "oc_sub oc_b30 10"
  by (oc_eval oc_c30_0010)

lemma oc_c30_0011: "oc_sub oc_b30 11"
  by (oc_eval oc_c30_0011)

lemma oc_c30_0012: "oc_sub oc_b30 12"
  by (oc_eval oc_c30_0012)

lemma oc_c30_0013: "oc_sub oc_b30 13"
  by (oc_eval oc_c30_0013)

lemma oc_c30_0014: "oc_sub oc_b30 14"
  by (oc_eval oc_c30_0014)

lemma oc_c30_0015: "oc_sub oc_b30 15"
  by (oc_eval oc_c30_0015)

lemma upt_c30_000: "[0..<16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
  by (simp add: upt_rec)

lemma sec_c30_000: "\<forall>j\<in>{16 * 0..<16 * 0 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 0..<16 * 0 + 16}"
  then have "j \<in> set [0..<16]" unfolding set_upt by simp
  then have "j \<in> set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]" unfolding upt_c30_000 .
  then show "oc_sub oc_b30 j" using oc_c30_0000 oc_c30_0001 oc_c30_0002 oc_c30_0003 oc_c30_0004 oc_c30_0005 oc_c30_0006 oc_c30_0007 oc_c30_0008 oc_c30_0009 oc_c30_0010 oc_c30_0011 oc_c30_0012 oc_c30_0013 oc_c30_0014 oc_c30_0015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
