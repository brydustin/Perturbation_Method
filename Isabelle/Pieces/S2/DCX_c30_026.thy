theory DCX_c30_026
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0416: "dc_sub dc_b30 416"
  by (dc_eval dc_c30_0416)

lemma dc_c30_0417: "dc_sub dc_b30 417"
  by (dc_eval dc_c30_0417)

lemma dc_c30_0418: "dc_sub dc_b30 418"
  by (dc_eval dc_c30_0418)

lemma dc_c30_0419: "dc_sub dc_b30 419"
  by (dc_eval dc_c30_0419)

lemma dc_c30_0420: "dc_sub dc_b30 420"
  by (dc_eval dc_c30_0420)

lemma dc_c30_0421: "dc_sub dc_b30 421"
  by (dc_eval dc_c30_0421)

lemma dc_c30_0422: "dc_sub dc_b30 422"
  by (dc_eval dc_c30_0422)

lemma dc_c30_0423: "dc_sub dc_b30 423"
  by (dc_eval dc_c30_0423)

lemma dc_c30_0424: "dc_sub dc_b30 424"
  by (dc_eval dc_c30_0424)

lemma dc_c30_0425: "dc_sub dc_b30 425"
  by (dc_eval dc_c30_0425)

lemma dc_c30_0426: "dc_sub dc_b30 426"
  by (dc_eval dc_c30_0426)

lemma dc_c30_0427: "dc_sub dc_b30 427"
  by (dc_eval dc_c30_0427)

lemma dc_c30_0428: "dc_sub dc_b30 428"
  by (dc_eval dc_c30_0428)

lemma dc_c30_0429: "dc_sub dc_b30 429"
  by (dc_eval dc_c30_0429)

lemma dc_c30_0430: "dc_sub dc_b30 430"
  by (dc_eval dc_c30_0430)

lemma dc_c30_0431: "dc_sub dc_b30 431"
  by (dc_eval dc_c30_0431)

lemma upt_c30_026: "[416..<432] = [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]"
  by (simp add: upt_rec)

lemma sec_c30_026: "\<forall>j\<in>{16 * 26..<16 * 26 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 26..<16 * 26 + 16}"
  then have "j \<in> set [416..<432]" unfolding set_upt by simp
  then have "j \<in> set [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431]" unfolding upt_c30_026 .
  then show "dc_sub dc_b30 j" using dc_c30_0416 dc_c30_0417 dc_c30_0418 dc_c30_0419 dc_c30_0420 dc_c30_0421 dc_c30_0422 dc_c30_0423 dc_c30_0424 dc_c30_0425 dc_c30_0426 dc_c30_0427 dc_c30_0428 dc_c30_0429 dc_c30_0430 dc_c30_0431
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end
