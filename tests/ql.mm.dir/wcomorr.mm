include "wo.mm"
include "wleo.mm"
include "wlecom.mm"

theorem wcomorr
  param wva: term a
  param wvb: term b


  assert |- C ( a , ( a v b ) ) = 1

  proof
    wva
    wva
    wvb
    wo
    wva
    wvb
    wleo
    wlecom
end
