include "wo.mm"
include "leo.mm"
include "lecom.mm"

theorem comorr
  let wva: term a
  let wvb: term b


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
