include "wfn.mm"
include "ccnv.mm"
include "wa.mm"
include "wf1o.mm"
include "wrel.mm"
include "fnrel.mm"
include "wceq.mm"
include "wi.mm"
include "dfrel2.mm"
include "fneq1.mm"
include "biimprd.mm"
include "sylbi.mm"
include "mpcom.mm"
include "anim2i.mm"
include "ancoms.mm"
include "dff1o4.mm"
include "3imtr4i.mm"

theorem f1ocnv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B -> `' F : B -1-1-onto-> A )

  proof
    cF
    cA
    wfn
    #
    cF
    ccnv
    #
    cB
    wfn
    #
    wa
    @2
    @1
    ccnv
    #
    cA
    wfn
    #
    wa
    #
    cA
    cB
    cF
    wf1o
    cB
    cA
    @1
    wf1o
    @2
    @0
    @5
    @0
    @4
    @2
    cF
    wrel
    #
    @0
    @4
    cA
    cF
    fnrel
    @6
    @3
    cF
    wceq
    #
    @0
    @4
    wi
    cF
    dfrel2
    @7
    @4
    @0
    cA
    @3
    cF
    fneq1
    biimprd
    sylbi
    mpcom
    anim2i
    ancoms
    cA
    cB
    cF
    dff1o4
    cB
    cA
    @1
    dff1o4
    3imtr4i
end
