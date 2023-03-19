include "wo.mm"
include "comorr.mm"
include "oridm.mm"
include "cbtr.mm"

theorem comid
  let wva: term a


  assert |- a C a

  proof
    wva
    wva
    wva
    wo
    wva
    wva
    wva
    comorr
    wva
    oridm
    cbtr
end
