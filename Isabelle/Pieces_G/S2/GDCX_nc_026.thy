theory GDCX_nc_026
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0416: "gdc_sub None 416"
  by (gdc_eval gdc_nc_0416)

lemma gdc_nc_0417: "gdc_sub None 417"
  by (gdc_eval gdc_nc_0417)

lemma gdc_nc_0418: "gdc_sub None 418"
  by (gdc_eval gdc_nc_0418)

lemma gdc_nc_0419: "gdc_sub None 419"
  by (gdc_eval gdc_nc_0419)

lemma gdc_nc_0420: "gdc_sub None 420"
  by (gdc_eval gdc_nc_0420)

lemma gdc_nc_0421: "gdc_sub None 421"
  by (gdc_eval gdc_nc_0421)

lemma gdc_nc_0422: "gdc_sub None 422"
  by (gdc_eval gdc_nc_0422)

lemma gdc_nc_0423: "gdc_sub None 423"
  by (gdc_eval gdc_nc_0423)

lemma gdc_nc_0424: "gdc_sub None 424"
  by (gdc_eval gdc_nc_0424)

lemma gdc_nc_0425: "gdc_sub None 425"
  by (gdc_eval gdc_nc_0425)

lemma gdc_nc_0426: "gdc_sub None 426"
  by (gdc_eval gdc_nc_0426)

lemma gdc_nc_0427: "gdc_sub None 427"
  by (gdc_eval gdc_nc_0427)

lemma gdc_nc_0428: "gdc_sub None 428"
  by (gdc_eval gdc_nc_0428)

lemma gdc_nc_0429: "gdc_sub None 429"
  by (gdc_eval gdc_nc_0429)

lemma gdc_nc_0430: "gdc_sub None 430"
  by (gdc_eval gdc_nc_0430)

lemma gdc_nc_0431: "gdc_sub None 431"
  by (gdc_eval gdc_nc_0431)

lemma gupt_nc_026: "[416..<432] = [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]"
  by (simp add: upt_rec)

lemma gsec_nc_026: "\<forall>j\<in>{16 * 26..<16 * 26 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 26..<16 * 26 + 16}"
  then have "j \<in> set [416..<432]" unfolding set_upt by simp
  then have "j \<in> set [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]" unfolding gupt_nc_026 .
  then show "gdc_sub None j" using gdc_nc_0416 gdc_nc_0417 gdc_nc_0418 gdc_nc_0419 gdc_nc_0420 gdc_nc_0421 gdc_nc_0422 gdc_nc_0423 gdc_nc_0424 gdc_nc_0425 gdc_nc_0426 gdc_nc_0427 gdc_nc_0428 gdc_nc_0429 gdc_nc_0430 gdc_nc_0431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
