theory DCS_0_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_000: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 0) (-8)) (Float (int 0 + 1) (-8))"
  by eval

lemma dc_nc_000: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 0) (-8)) (Float (int 0 + 1) (-8))"
  by eval

lemma dc_c30_001: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 1) (-8)) (Float (int 1 + 1) (-8))"
  by eval

lemma dc_nc_001: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 1) (-8)) (Float (int 1 + 1) (-8))"
  by eval

lemma dc_c30_002: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 2) (-8)) (Float (int 2 + 1) (-8))"
  by eval

lemma dc_nc_002: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 2) (-8)) (Float (int 2 + 1) (-8))"
  by eval

lemma dc_c30_003: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 3) (-8)) (Float (int 3 + 1) (-8))"
  by eval

lemma dc_nc_003: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 3) (-8)) (Float (int 3 + 1) (-8))"
  by eval

end
