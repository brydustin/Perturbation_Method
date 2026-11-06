theory DCS_3_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_060: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 60) (-8)) (Float (int 60 + 1) (-8))"
  by eval

lemma dc_nc_060: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 60) (-8)) (Float (int 60 + 1) (-8))"
  by eval

lemma dc_c30_061: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 61) (-8)) (Float (int 61 + 1) (-8))"
  by eval

lemma dc_nc_061: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 61) (-8)) (Float (int 61 + 1) (-8))"
  by eval

lemma dc_c30_062: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 62) (-8)) (Float (int 62 + 1) (-8))"
  by eval

lemma dc_nc_062: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 62) (-8)) (Float (int 62 + 1) (-8))"
  by eval

lemma dc_c30_063: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 63) (-8)) (Float (int 63 + 1) (-8))"
  by eval

lemma dc_nc_063: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 63) (-8)) (Float (int 63 + 1) (-8))"
  by eval

end
