theory GOCX_nc_026
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0416: "goc_sub None 416"
  by (goc_eval goc_nc_0416)

lemma goc_nc_0417: "goc_sub None 417"
  by (goc_eval goc_nc_0417)

lemma goc_nc_0418: "goc_sub None 418"
  by (goc_eval goc_nc_0418)

lemma goc_nc_0419: "goc_sub None 419"
  by (goc_eval goc_nc_0419)

lemma goc_nc_0420: "goc_sub None 420"
  by (goc_eval goc_nc_0420)

lemma goc_nc_0421: "goc_sub None 421"
  by (goc_eval goc_nc_0421)

lemma goc_nc_0422: "goc_sub None 422"
  by (goc_eval goc_nc_0422)

lemma goc_nc_0423: "goc_sub None 423"
  by (goc_eval goc_nc_0423)

lemma goc_nc_0424: "goc_sub None 424"
  by (goc_eval goc_nc_0424)

lemma goc_nc_0425: "goc_sub None 425"
  by (goc_eval goc_nc_0425)

lemma goc_nc_0426: "goc_sub None 426"
  by (goc_eval goc_nc_0426)

lemma goc_nc_0427: "goc_sub None 427"
  by (goc_eval goc_nc_0427)

lemma goc_nc_0428: "goc_sub None 428"
  by (goc_eval goc_nc_0428)

lemma goc_nc_0429: "goc_sub None 429"
  by (goc_eval goc_nc_0429)

lemma goc_nc_0430: "goc_sub None 430"
  by (goc_eval goc_nc_0430)

lemma goc_nc_0431: "goc_sub None 431"
  by (goc_eval goc_nc_0431)

lemma gupt_nc_026: "[416..<432] = [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]"
  by (simp add: upt_rec)

lemma gsec_nc_026: "\<forall>j\<in>{16 * 26..<16 * 26 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 26..<16 * 26 + 16}"
  then have "j \<in> set [416..<432]" unfolding set_upt by simp
  then have "j \<in> set [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]" unfolding gupt_nc_026 .
  then show "goc_sub None j" using goc_nc_0416 goc_nc_0417 goc_nc_0418 goc_nc_0419 goc_nc_0420 goc_nc_0421 goc_nc_0422 goc_nc_0423 goc_nc_0424 goc_nc_0425 goc_nc_0426 goc_nc_0427 goc_nc_0428 goc_nc_0429 goc_nc_0430 goc_nc_0431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
