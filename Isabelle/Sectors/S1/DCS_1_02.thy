theory DCS_1_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_024: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 24) (-8)) (Float (int 24 + 1) (-8))"
  by eval

lemma dc_nc_024: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 24) (-8)) (Float (int 24 + 1) (-8))"
  by eval

lemma dc_c30_025: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 25) (-8)) (Float (int 25 + 1) (-8))"
  by eval

lemma dc_nc_025: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 25) (-8)) (Float (int 25 + 1) (-8))"
  by eval

lemma dc_c30_026: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 26) (-8)) (Float (int 26 + 1) (-8))"
  by eval

lemma dc_nc_026: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 26) (-8)) (Float (int 26 + 1) (-8))"
  by eval

lemma dc_c30_027: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 27) (-8)) (Float (int 27 + 1) (-8))"
  by eval

lemma dc_nc_027: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 27) (-8)) (Float (int 27 + 1) (-8))"
  by eval

end
