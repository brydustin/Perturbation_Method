theory GDCX_nc_032
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0512: "gdc_sub None 512"
  by (gdc_eval gdc_nc_0512)

lemma gdc_nc_0513: "gdc_sub None 513"
  by (gdc_eval gdc_nc_0513)

lemma gdc_nc_0514: "gdc_sub None 514"
  by (gdc_eval gdc_nc_0514)

lemma gdc_nc_0515: "gdc_sub None 515"
  by (gdc_eval gdc_nc_0515)

lemma gdc_nc_0516: "gdc_sub None 516"
  by (gdc_eval gdc_nc_0516)

lemma gdc_nc_0517: "gdc_sub None 517"
  by (gdc_eval gdc_nc_0517)

lemma gdc_nc_0518: "gdc_sub None 518"
  by (gdc_eval gdc_nc_0518)

lemma gdc_nc_0519: "gdc_sub None 519"
  by (gdc_eval gdc_nc_0519)

lemma gdc_nc_0520: "gdc_sub None 520"
  by (gdc_eval gdc_nc_0520)

lemma gdc_nc_0521: "gdc_sub None 521"
  by (gdc_eval gdc_nc_0521)

lemma gdc_nc_0522: "gdc_sub None 522"
  by (gdc_eval gdc_nc_0522)

lemma gdc_nc_0523: "gdc_sub None 523"
  by (gdc_eval gdc_nc_0523)

lemma gdc_nc_0524: "gdc_sub None 524"
  by (gdc_eval gdc_nc_0524)

lemma gdc_nc_0525: "gdc_sub None 525"
  by (gdc_eval gdc_nc_0525)

lemma gdc_nc_0526: "gdc_sub None 526"
  by (gdc_eval gdc_nc_0526)

lemma gdc_nc_0527: "gdc_sub None 527"
  by (gdc_eval gdc_nc_0527)

lemma gupt_nc_032: "[512..<528] = [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]"
  by (simp add: upt_rec)

lemma gsec_nc_032: "\<forall>j\<in>{16 * 32..<16 * 32 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 32..<16 * 32 + 16}"
  then have "j \<in> set [512..<528]" unfolding set_upt by simp
  then have "j \<in> set [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527]" unfolding gupt_nc_032 .
  then show "gdc_sub None j" using gdc_nc_0512 gdc_nc_0513 gdc_nc_0514 gdc_nc_0515 gdc_nc_0516 gdc_nc_0517 gdc_nc_0518 gdc_nc_0519 gdc_nc_0520 gdc_nc_0521 gdc_nc_0522 gdc_nc_0523 gdc_nc_0524 gdc_nc_0525 gdc_nc_0526 gdc_nc_0527
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
