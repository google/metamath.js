include "nom14.mm"

theorem lem3.3.7i4e3
  param wva: term a
  param wvb: term b


  assert |- ( a ->4 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wvb
    nom14
end
