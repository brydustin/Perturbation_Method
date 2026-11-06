theory DCS_0_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_012: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 12) (-8)) (Float (int 12 + 1) (-8))"
  by eval

lemma dc_nc_012: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 12) (-8)) (Float (int 12 + 1) (-8))"
  by eval

lemma dc_c30_013: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 13) (-8)) (Float (int 13 + 1) (-8))"
  by eval

lemma dc_nc_013: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 13) (-8)) (Float (int 13 + 1) (-8))"
  by eval

lemma dc_c30_014: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 14) (-8)) (Float (int 14 + 1) (-8))"
  by eval

lemma dc_nc_014: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 14) (-8)) (Float (int 14 + 1) (-8))"
  by eval

lemma dc_c30_015: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 15) (-8)) (Float (int 15 + 1) (-8))"
  by eval

lemma dc_nc_015: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 15) (-8)) (Float (int 15 + 1) (-8))"
  by eval

end
