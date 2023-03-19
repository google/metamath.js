include "wa.mm"
include "wlea.mm"
include "wlecom.mm"

theorem wcoman1
  let wva: term a
  let wvb: term b


  assert |- C ( ( a ^ b ) , a ) = 1

  proof
    wva
    wvb
    wa
    wva
    wva
    wvb
    wlea
    wlecom
end
