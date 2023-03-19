include "csn.mm"
include "wf.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "crn.mm"
include "wceq.mm"
include "wfo.mm"
include "wn.mm"
include "wrel.mm"
include "wb.mm"
include "frel.mm"
include "relrn0.mm"
include "necon3abid.mm"
include "syl.mm"
include "wss.mm"
include "wo.mm"
include "frn.mm"
include "sssn.mm"
include "sylib.mm"
include "ord.mm"
include "sylbid.mm"
include "imdistani.mm"
include "dffo2.mm"
include "sylibr.mm"

theorem foconst
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F : A --> { B } /\ F =/= (/) ) -> F : A -onto-> { B } )

  proof
    cA
    cB
    csn
    #
    cF
    wf
    #
    cF
    c0
    wne
    #
    wa
    @1
    cF
    crn
    #
    @0
    wceq
    #
    wa
    cA
    @0
    cF
    wfo
    @1
    @2
    @4
    @1
    @2
    @3
    c0
    wceq
    #
    wn
    #
    @4
    @1
    cF
    wrel
    #
    @2
    @6
    wb
    cA
    @0
    cF
    frel
    @7
    @5
    cF
    c0
    cF
    relrn0
    necon3abid
    syl
    @1
    @5
    @4
    @1
    @3
    @0
    wss
    @5
    @4
    wo
    cA
    @0
    cF
    frn
    @3
    cB
    sssn
    sylib
    ord
    sylbid
    imdistani
    cA
    @0
    cF
    dffo2
    sylibr
end
