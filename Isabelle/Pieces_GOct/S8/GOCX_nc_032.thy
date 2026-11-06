theory GOCX_nc_032
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0512: "goc_sub None 512"
  by (goc_eval goc_nc_0512)

lemma goc_nc_0513: "goc_sub None 513"
  by (goc_eval goc_nc_0513)

lemma goc_nc_0514: "goc_sub None 514"
  by (goc_eval goc_nc_0514)

lemma goc_nc_0515: "goc_sub None 515"
  by (goc_eval goc_nc_0515)

lemma goc_nc_0516: "goc_sub None 516"
  by (goc_eval goc_nc_0516)

lemma goc_nc_0517: "goc_sub None 517"
  by (goc_eval goc_nc_0517)

lemma goc_nc_0518: "goc_sub None 518"
  by (goc_eval goc_nc_0518)

lemma goc_nc_0519: "goc_sub None 519"
  by (goc_eval goc_nc_0519)

lemma goc_nc_0520: "goc_sub None 520"
  by (goc_eval goc_nc_0520)

lemma goc_nc_0521: "goc_sub None 521"
  by (goc_eval goc_nc_0521)

lemma goc_nc_0522: "goc_sub None 522"
  by (goc_eval goc_nc_0522)

lemma goc_nc_0523: "goc_sub None 523"
  by (goc_eval goc_nc_0523)

lemma goc_nc_0524: "goc_sub None 524"
  by (goc_eval goc_nc_0524)

lemma goc_nc_0525: "goc_sub None 525"
  by (goc_eval goc_nc_0525)

lemma goc_nc_0526: "goc_sub None 526"
  by (goc_eval goc_nc_0526)

lemma goc_nc_0527: "goc_sub None 527"
  by (goc_eval goc_nc_0527)

lemma gupt_nc_032: "[512..<528] = [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]"
  by (simp add: upt_rec)

lemma gsec_nc_032: "\<forall>j\<in>{16 * 32..<16 * 32 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 32..<16 * 32 + 16}"
  then have "j \<in> set [512..<528]" unfolding set_upt by simp
  then have "j \<in> set [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]" unfolding gupt_nc_032 .
  then show "goc_sub None j" using goc_nc_0512 goc_nc_0513 goc_nc_0514 goc_nc_0515 goc_nc_0516 goc_nc_0517 goc_nc_0518 goc_nc_0519 goc_nc_0520 goc_nc_0521 goc_nc_0522 goc_nc_0523 goc_nc_0524 goc_nc_0525 goc_nc_0526 goc_nc_0527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
