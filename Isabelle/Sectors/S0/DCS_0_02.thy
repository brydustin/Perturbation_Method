theory DCS_0_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_008: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 8) (-8)) (Float (int 8 + 1) (-8))"
  by eval

lemma dc_nc_008: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 8) (-8)) (Float (int 8 + 1) (-8))"
  by eval

lemma dc_c30_009: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 9) (-8)) (Float (int 9 + 1) (-8))"
  by eval

lemma dc_nc_009: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 9) (-8)) (Float (int 9 + 1) (-8))"
  by eval

lemma dc_c30_010: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 10) (-8)) (Float (int 10 + 1) (-8))"
  by eval

lemma dc_nc_010: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 10) (-8)) (Float (int 10 + 1) (-8))"
  by eval

lemma dc_c30_011: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 11) (-8)) (Float (int 11 + 1) (-8))"
  by eval

lemma dc_nc_011: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 11) (-8)) (Float (int 11 + 1) (-8))"
  by eval

end
