theory DCS_3_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_056: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 56) (-8)) (Float (int 56 + 1) (-8))"
  by eval

lemma dc_nc_056: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 56) (-8)) (Float (int 56 + 1) (-8))"
  by eval

lemma dc_c30_057: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 57) (-8)) (Float (int 57 + 1) (-8))"
  by eval

lemma dc_nc_057: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 57) (-8)) (Float (int 57 + 1) (-8))"
  by eval

lemma dc_c30_058: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 58) (-8)) (Float (int 58 + 1) (-8))"
  by eval

lemma dc_nc_058: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 58) (-8)) (Float (int 58 + 1) (-8))"
  by eval

lemma dc_c30_059: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 59) (-8)) (Float (int 59 + 1) (-8))"
  by eval

lemma dc_nc_059: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 59) (-8)) (Float (int 59 + 1) (-8))"
  by eval

end
