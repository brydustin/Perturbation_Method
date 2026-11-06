theory DCS_12_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_196: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 196) (-8)) (Float (int 196 + 1) (-8))"
  by eval

lemma dc_nc_196: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 196) (-8)) (Float (int 196 + 1) (-8))"
  by eval

lemma dc_c30_197: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 197) (-8)) (Float (int 197 + 1) (-8))"
  by eval

lemma dc_nc_197: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 197) (-8)) (Float (int 197 + 1) (-8))"
  by eval

lemma dc_c30_198: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 198) (-8)) (Float (int 198 + 1) (-8))"
  by eval

lemma dc_nc_198: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 198) (-8)) (Float (int 198 + 1) (-8))"
  by eval

lemma dc_c30_199: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 199) (-8)) (Float (int 199 + 1) (-8))"
  by eval

lemma dc_nc_199: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 199) (-8)) (Float (int 199 + 1) (-8))"
  by eval

end
