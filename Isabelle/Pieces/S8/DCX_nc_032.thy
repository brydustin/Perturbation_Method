theory DCX_nc_032
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0512: "dc_sub None 512"
  by (dc_eval dc_nc_0512)

lemma dc_nc_0513: "dc_sub None 513"
  by (dc_eval dc_nc_0513)

lemma dc_nc_0514: "dc_sub None 514"
  by (dc_eval dc_nc_0514)

lemma dc_nc_0515: "dc_sub None 515"
  by (dc_eval dc_nc_0515)

lemma dc_nc_0516: "dc_sub None 516"
  by (dc_eval dc_nc_0516)

lemma dc_nc_0517: "dc_sub None 517"
  by (dc_eval dc_nc_0517)

lemma dc_nc_0518: "dc_sub None 518"
  by (dc_eval dc_nc_0518)

lemma dc_nc_0519: "dc_sub None 519"
  by (dc_eval dc_nc_0519)

lemma dc_nc_0520: "dc_sub None 520"
  by (dc_eval dc_nc_0520)

lemma dc_nc_0521: "dc_sub None 521"
  by (dc_eval dc_nc_0521)

lemma dc_nc_0522: "dc_sub None 522"
  by (dc_eval dc_nc_0522)

lemma dc_nc_0523: "dc_sub None 523"
  by (dc_eval dc_nc_0523)

lemma dc_nc_0524: "dc_sub None 524"
  by (dc_eval dc_nc_0524)

lemma dc_nc_0525: "dc_sub None 525"
  by (dc_eval dc_nc_0525)

lemma dc_nc_0526: "dc_sub None 526"
  by (dc_eval dc_nc_0526)

lemma dc_nc_0527: "dc_sub None 527"
  by (dc_eval dc_nc_0527)

lemma upt_nc_032: "[512..<528] = [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]"
  by (simp add: upt_rec)

lemma sec_nc_032: "\<forall>j\<in>{16 * 32..<16 * 32 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 32..<16 * 32 + 16}"
  then have "j \<in> set [512..<528]" unfolding set_upt by simp
  then have "j \<in> set [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]" unfolding upt_nc_032 .
  then show "dc_sub None j" using dc_nc_0512 dc_nc_0513 dc_nc_0514 dc_nc_0515 dc_nc_0516 dc_nc_0517 dc_nc_0518 dc_nc_0519 dc_nc_0520 dc_nc_0521 dc_nc_0522 dc_nc_0523 dc_nc_0524 dc_nc_0525 dc_nc_0526 dc_nc_0527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
