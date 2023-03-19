include "wo.mm"
include "comor2.mm"
include "comcom.mm"

theorem comorr2
  let wva: term a
  let wvb: term b


  assert |- b C ( a v b )

  proof
    wva
    wvb
    wo
    wvb
    wva
    wvb
    comor2
    comcom
end
