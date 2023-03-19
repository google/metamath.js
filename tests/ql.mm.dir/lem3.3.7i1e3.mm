include "nom11.mm"

theorem lem3.3.7i1e3
  param wva: term a
  param wvb: term b


  assert |- ( a ->1 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wvb
    nom11
end
