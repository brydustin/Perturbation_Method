theory DCX_c30_032
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0512: "dc_sub dc_b30 512"
  by (dc_eval dc_c30_0512)

lemma dc_c30_0513: "dc_sub dc_b30 513"
  by (dc_eval dc_c30_0513)

lemma dc_c30_0514: "dc_sub dc_b30 514"
  by (dc_eval dc_c30_0514)

lemma dc_c30_0515: "dc_sub dc_b30 515"
  by (dc_eval dc_c30_0515)

lemma dc_c30_0516: "dc_sub dc_b30 516"
  by (dc_eval dc_c30_0516)

lemma dc_c30_0517: "dc_sub dc_b30 517"
  by (dc_eval dc_c30_0517)

lemma dc_c30_0518: "dc_sub dc_b30 518"
  by (dc_eval dc_c30_0518)

lemma dc_c30_0519: "dc_sub dc_b30 519"
  by (dc_eval dc_c30_0519)

lemma dc_c30_0520: "dc_sub dc_b30 520"
  by (dc_eval dc_c30_0520)

lemma dc_c30_0521: "dc_sub dc_b30 521"
  by (dc_eval dc_c30_0521)

lemma dc_c30_0522: "dc_sub dc_b30 522"
  by (dc_eval dc_c30_0522)

lemma dc_c30_0523: "dc_sub dc_b30 523"
  by (dc_eval dc_c30_0523)

lemma dc_c30_0524: "dc_sub dc_b30 524"
  by (dc_eval dc_c30_0524)

lemma dc_c30_0525: "dc_sub dc_b30 525"
  by (dc_eval dc_c30_0525)

lemma dc_c30_0526: "dc_sub dc_b30 526"
  by (dc_eval dc_c30_0526)

lemma dc_c30_0527: "dc_sub dc_b30 527"
  by (dc_eval dc_c30_0527)

lemma upt_c30_032: "[512..<528] = [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]"
  by (simp add: upt_rec)

lemma sec_c30_032: "\<forall>j\<in>{16 * 32..<16 * 32 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 32..<16 * 32 + 16}"
  then have "j \<in> set [512..<528]" unfolding set_upt by simp
  then have "j \<in> set [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]" unfolding upt_c30_032 .
  then show "dc_sub dc_b30 j" using dc_c30_0512 dc_c30_0513 dc_c30_0514 dc_c30_0515 dc_c30_0516 dc_c30_0517 dc_c30_0518 dc_c30_0519 dc_c30_0520 dc_c30_0521 dc_c30_0522 dc_c30_0523 dc_c30_0524 dc_c30_0525 dc_c30_0526 dc_c30_0527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
