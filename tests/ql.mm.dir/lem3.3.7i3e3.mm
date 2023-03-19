include "nom13.mm"

theorem lem3.3.7i3e3
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wvb
    nom13
end
