include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "wn.mm"
include "wo.mm"
include "wceq.mm"
include "ianor.mm"
include "ndmfv.mm"
include "nfunsn.mm"
include "jaoi.mm"
include "sylbi.mm"
include "necon1ai.mm"

theorem fvfundmfvn0
  let cA: class A
  let cF: class F


  assert |- ( ( F ` A ) =/= (/) -> ( A e. dom F /\ Fun ( F |` { A } ) ) )

  proof
    cA
    cF
    cdm
    wcel
    #
    cF
    cA
    csn
    cres
    wfun
    #
    wa
    #
    cA
    cF
    cfv
    #
    c0
    @2
    wn
    @0
    wn
    #
    @1
    wn
    #
    wo
    @3
    c0
    wceq
    #
    @0
    @1
    ianor
    @4
    @6
    @5
    cA
    cF
    ndmfv
    cA
    cF
    nfunsn
    jaoi
    sylbi
    necon1ai
end
