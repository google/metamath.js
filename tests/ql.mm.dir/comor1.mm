include "wo.mm"
include "comorr.mm"
include "comcom.mm"

theorem comor1
  let wva: term a
  let wvb: term b


  assert |- ( a v b ) C a

  proof
    wva
    wva
    wvb
    wo
    wva
    wvb
    comorr
    comcom
end
