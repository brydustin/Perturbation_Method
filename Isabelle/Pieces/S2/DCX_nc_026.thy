theory DCX_nc_026
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0416: "dc_sub None 416"
  by (dc_eval dc_nc_0416)

lemma dc_nc_0417: "dc_sub None 417"
  by (dc_eval dc_nc_0417)

lemma dc_nc_0418: "dc_sub None 418"
  by (dc_eval dc_nc_0418)

lemma dc_nc_0419: "dc_sub None 419"
  by (dc_eval dc_nc_0419)

lemma dc_nc_0420: "dc_sub None 420"
  by (dc_eval dc_nc_0420)

lemma dc_nc_0421: "dc_sub None 421"
  by (dc_eval dc_nc_0421)

lemma dc_nc_0422: "dc_sub None 422"
  by (dc_eval dc_nc_0422)

lemma dc_nc_0423: "dc_sub None 423"
  by (dc_eval dc_nc_0423)

lemma dc_nc_0424: "dc_sub None 424"
  by (dc_eval dc_nc_0424)

lemma dc_nc_0425: "dc_sub None 425"
  by (dc_eval dc_nc_0425)

lemma dc_nc_0426: "dc_sub None 426"
  by (dc_eval dc_nc_0426)

lemma dc_nc_0427: "dc_sub None 427"
  by (dc_eval dc_nc_0427)

lemma dc_nc_0428: "dc_sub None 428"
  by (dc_eval dc_nc_0428)

lemma dc_nc_0429: "dc_sub None 429"
  by (dc_eval dc_nc_0429)

lemma dc_nc_0430: "dc_sub None 430"
  by (dc_eval dc_nc_0430)

lemma dc_nc_0431: "dc_sub None 431"
  by (dc_eval dc_nc_0431)

lemma upt_nc_026: "[416..<432] = [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]"
  by (simp add: upt_rec)

lemma sec_nc_026: "\<forall>j\<in>{16 * 26..<16 * 26 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 26..<16 * 26 + 16}"
  then have "j \<in> set [416..<432]" unfolding set_upt by simp
  then have "j \<in> set [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]" unfolding upt_nc_026 .
  then show "dc_sub None j" using dc_nc_0416 dc_nc_0417 dc_nc_0418 dc_nc_0419 dc_nc_0420 dc_nc_0421 dc_nc_0422 dc_nc_0423 dc_nc_0424 dc_nc_0425 dc_nc_0426 dc_nc_0427 dc_nc_0428 dc_nc_0429 dc_nc_0430 dc_nc_0431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
