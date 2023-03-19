include "wo.mm"
include "leo.mm"
include "lecom.mm"

theorem comorr
  param wva: term a
  param wvb: term b


  assert |- a C ( a v b )

  proof
    wva
    wva
    wvb
    wo
    wva
    wvb
    leo
    lecom
end
