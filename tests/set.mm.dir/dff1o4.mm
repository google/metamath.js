include "wf1o.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "dff1o2.mm"
include "3anass.mm"
include "cdm.mm"
include "df-rn.mm"
include "eqeq1i.mm"
include "anbi2i.mm"
include "df-fn.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem dff1o4
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B <-> ( F Fn A /\ `' F Fn B ) )

  proof
    cA
    cB
    cF
    wf1o
    cF
    cA
    wfn
    #
    cF
    ccnv
    #
    wfun
    #
    cF
    crn
    #
    cB
    wceq
    #
    w3a
    @0
    @2
    @4
    wa
    #
    wa
    @0
    @1
    cB
    wfn
    #
    wa
    cA
    cB
    cF
    dff1o2
    @0
    @2
    @4
    3anass
    @5
    @6
    @0
    @5
    @2
    @1
    cdm
    #
    cB
    wceq
    #
    wa
    @6
    @4
    @8
    @2
    @3
    @7
    cB
    cF
    df-rn
    eqeq1i
    anbi2i
    @1
    cB
    df-fn
    bitr4i
    anbi2i
    3bitri
end
