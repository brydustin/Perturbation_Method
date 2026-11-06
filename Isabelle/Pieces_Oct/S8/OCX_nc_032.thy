theory OCX_nc_032
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0512: "oc_sub None 512"
  by (oc_eval oc_nc_0512)

lemma oc_nc_0513: "oc_sub None 513"
  by (oc_eval oc_nc_0513)

lemma oc_nc_0514: "oc_sub None 514"
  by (oc_eval oc_nc_0514)

lemma oc_nc_0515: "oc_sub None 515"
  by (oc_eval oc_nc_0515)

lemma oc_nc_0516: "oc_sub None 516"
  by (oc_eval oc_nc_0516)

lemma oc_nc_0517: "oc_sub None 517"
  by (oc_eval oc_nc_0517)

lemma oc_nc_0518: "oc_sub None 518"
  by (oc_eval oc_nc_0518)

lemma oc_nc_0519: "oc_sub None 519"
  by (oc_eval oc_nc_0519)

lemma oc_nc_0520: "oc_sub None 520"
  by (oc_eval oc_nc_0520)

lemma oc_nc_0521: "oc_sub None 521"
  by (oc_eval oc_nc_0521)

lemma oc_nc_0522: "oc_sub None 522"
  by (oc_eval oc_nc_0522)

lemma oc_nc_0523: "oc_sub None 523"
  by (oc_eval oc_nc_0523)

lemma oc_nc_0524: "oc_sub None 524"
  by (oc_eval oc_nc_0524)

lemma oc_nc_0525: "oc_sub None 525"
  by (oc_eval oc_nc_0525)

lemma oc_nc_0526: "oc_sub None 526"
  by (oc_eval oc_nc_0526)

lemma oc_nc_0527: "oc_sub None 527"
  by (oc_eval oc_nc_0527)

lemma upt_nc_032: "[512..<528] = [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]"
  by (simp add: upt_rec)

lemma sec_nc_032: "\<forall>j\<in>{16 * 32..<16 * 32 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 32..<16 * 32 + 16}"
  then have "j \<in> set [512..<528]" unfolding set_upt by simp
  then have "j \<in> set [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]" unfolding upt_nc_032 .
  then show "oc_sub None j" using oc_nc_0512 oc_nc_0513 oc_nc_0514 oc_nc_0515 oc_nc_0516 oc_nc_0517 oc_nc_0518 oc_nc_0519 oc_nc_0520 oc_nc_0521 oc_nc_0522 oc_nc_0523 oc_nc_0524 oc_nc_0525 oc_nc_0526 oc_nc_0527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
