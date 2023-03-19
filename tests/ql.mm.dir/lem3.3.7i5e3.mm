include "nom15.mm"

theorem lem3.3.7i5e3
  param wva: term a
  param wvb: term b


  assert |- ( a ->5 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wvb
    nom15
end
