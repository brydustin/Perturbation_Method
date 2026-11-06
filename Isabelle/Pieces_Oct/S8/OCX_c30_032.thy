theory OCX_c30_032
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0512: "oc_sub oc_b30 512"
  by (oc_eval oc_c30_0512)

lemma oc_c30_0513: "oc_sub oc_b30 513"
  by (oc_eval oc_c30_0513)

lemma oc_c30_0514: "oc_sub oc_b30 514"
  by (oc_eval oc_c30_0514)

lemma oc_c30_0515: "oc_sub oc_b30 515"
  by (oc_eval oc_c30_0515)

lemma oc_c30_0516: "oc_sub oc_b30 516"
  by (oc_eval oc_c30_0516)

lemma oc_c30_0517: "oc_sub oc_b30 517"
  by (oc_eval oc_c30_0517)

lemma oc_c30_0518: "oc_sub oc_b30 518"
  by (oc_eval oc_c30_0518)

lemma oc_c30_0519: "oc_sub oc_b30 519"
  by (oc_eval oc_c30_0519)

lemma oc_c30_0520: "oc_sub oc_b30 520"
  by (oc_eval oc_c30_0520)

lemma oc_c30_0521: "oc_sub oc_b30 521"
  by (oc_eval oc_c30_0521)

lemma oc_c30_0522: "oc_sub oc_b30 522"
  by (oc_eval oc_c30_0522)

lemma oc_c30_0523: "oc_sub oc_b30 523"
  by (oc_eval oc_c30_0523)

lemma oc_c30_0524: "oc_sub oc_b30 524"
  by (oc_eval oc_c30_0524)

lemma oc_c30_0525: "oc_sub oc_b30 525"
  by (oc_eval oc_c30_0525)

lemma oc_c30_0526: "oc_sub oc_b30 526"
  by (oc_eval oc_c30_0526)

lemma oc_c30_0527: "oc_sub oc_b30 527"
  by (oc_eval oc_c30_0527)

lemma upt_c30_032: "[512..<528] = [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]"
  by (simp add: upt_rec)

lemma sec_c30_032: "\<forall>j\<in>{16 * 32..<16 * 32 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 32..<16 * 32 + 16}"
  then have "j \<in> set [512..<528]" unfolding set_upt by simp
  then have "j \<in> set [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]" unfolding upt_c30_032 .
  then show "oc_sub oc_b30 j" using oc_c30_0512 oc_c30_0513 oc_c30_0514 oc_c30_0515 oc_c30_0516 oc_c30_0517 oc_c30_0518 oc_c30_0519 oc_c30_0520 oc_c30_0521 oc_c30_0522 oc_c30_0523 oc_c30_0524 oc_c30_0525 oc_c30_0526 oc_c30_0527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
