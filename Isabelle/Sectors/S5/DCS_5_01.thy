theory DCS_5_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_084: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 84) (-8)) (Float (int 84 + 1) (-8))"
  by eval

lemma dc_nc_084: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 84) (-8)) (Float (int 84 + 1) (-8))"
  by eval

lemma dc_c30_085: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 85) (-8)) (Float (int 85 + 1) (-8))"
  by eval

lemma dc_nc_085: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 85) (-8)) (Float (int 85 + 1) (-8))"
  by eval

lemma dc_c30_086: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 86) (-8)) (Float (int 86 + 1) (-8))"
  by eval

lemma dc_nc_086: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 86) (-8)) (Float (int 86 + 1) (-8))"
  by eval

lemma dc_c30_087: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 87) (-8)) (Float (int 87 + 1) (-8))"
  by eval

lemma dc_nc_087: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 87) (-8)) (Float (int 87 + 1) (-8))"
  by eval

end
