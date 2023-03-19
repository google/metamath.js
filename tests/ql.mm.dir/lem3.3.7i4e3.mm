include "nom14.mm"

theorem lem3.3.7i4e3
  let wva: term a
  let wvb: term b


  assert |- ( a ->4 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wvb
    nom14
end
