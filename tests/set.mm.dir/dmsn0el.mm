include "c0.mm"
include "wcel.mm"
include "csn.mm"
include "cdm.mm"
include "wne.mm"
include "cvv.mm"
include "cxp.mm"
include "wn.mm"
include "dmsnn0.mm"
include "0nelelxp.mm"
include "sylbir.mm"
include "necon4ai.mm"

theorem dmsn0el
  let cA: class A


  assert |- ( (/) e. A -> dom { A } = (/) )

  proof
    c0
    cA
    wcel
    #
    cA
    csn
    cdm
    #
    c0
    @1
    c0
    wne
    cA
    cvv
    cvv
    cxp
    wcel
    @0
    wn
    cA
    dmsnn0
    cvv
    cvv
    cA
    0nelelxp
    sylbir
    necon4ai
end
