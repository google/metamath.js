include "nom12.mm"

theorem lem3.3.7i2e3
  let wva: term a
  let wvb: term b


  assert |- ( a ->2 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wvb
    nom12
end
