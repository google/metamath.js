include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "wf1o.mm"
include "wfo.mm"
include "3anan32.mm"
include "dff1o2.mm"
include "df-fo.mm"
include "anbi1i.mm"
include "3bitr4i.mm"

theorem dff1o3
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B <-> ( F : A -onto-> B /\ Fun `' F ) )

  proof
    cF
    cA
    wfn
    #
    cF
    ccnv
    wfun
    #
    cF
    crn
    cB
    wceq
    #
    w3a
    @0
    @2
    wa
    #
    @1
    wa
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wfo
    #
    @1
    wa
    @0
    @1
    @2
    3anan32
    cA
    cB
    cF
    dff1o2
    @4
    @3
    @1
    cA
    cB
    cF
    df-fo
    anbi1i
    3bitr4i
end
