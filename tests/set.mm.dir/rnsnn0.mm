include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "csn.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "crn.mm"
include "dmsnn0.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "bitri.mm"

theorem rnsnn0
  let cA: class A


  assert |- ( A e. ( _V X. _V ) <-> ran { A } =/= (/) )

  proof
    cA
    cvv
    cvv
    cxp
    wcel
    cA
    csn
    #
    cdm
    #
    c0
    wne
    @0
    crn
    #
    c0
    wne
    cA
    dmsnn0
    @1
    c0
    @2
    c0
    @0
    dm0rn0
    necon3bii
    bitri
end
