theory DCS_12_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_200: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 200) (-8)) (Float (int 200 + 1) (-8))"
  by eval

lemma dc_nc_200: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 200) (-8)) (Float (int 200 + 1) (-8))"
  by eval

lemma dc_c30_201: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 201) (-8)) (Float (int 201 + 1) (-8))"
  by eval

lemma dc_nc_201: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 201) (-8)) (Float (int 201 + 1) (-8))"
  by eval

end
