include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "wfn.mm"
include "ccnv.mm"
include "wfun.mm"
include "crn.mm"
include "wceq.mm"
include "w3a.mm"
include "df-f1o.mm"
include "wf.mm"
include "df-f1.mm"
include "df-fo.mm"
include "anbi12i.mm"
include "anass.mm"
include "3anan12.mm"
include "anbi1i.mm"
include "wss.mm"
include "eqimss.mm"
include "df-f.mm"
include "biimpri.mm"
include "sylan2.mm"
include "3adant2.mm"
include "pm4.71i.mm"
include "ancom.mm"
include "3bitr4ri.mm"
include "bitri.mm"

theorem dff1o2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -1-1-onto-> B <-> ( F Fn A /\ Fun `' F /\ ran F = B ) )

  proof
    cA
    cB
    cF
    wf1o
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cF
    wfo
    #
    wa
    #
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
    #
    cB
    wceq
    #
    w3a
    #
    cA
    cB
    cF
    df-f1o
    @2
    cA
    cB
    cF
    wf
    #
    @4
    wa
    #
    @3
    @6
    wa
    #
    wa
    #
    @7
    @0
    @9
    @1
    @10
    cA
    cB
    cF
    df-f1
    cA
    cB
    cF
    df-fo
    anbi12i
    @11
    @8
    @4
    @10
    wa
    #
    wa
    #
    @7
    @8
    @4
    @10
    anass
    @7
    @8
    wa
    @12
    @8
    wa
    @7
    @13
    @7
    @12
    @8
    @3
    @4
    @6
    3anan12
    anbi1i
    @7
    @8
    @3
    @6
    @8
    @4
    @6
    @3
    @5
    cB
    wss
    #
    @8
    @5
    cB
    eqimss
    @8
    @3
    @14
    wa
    cA
    cB
    cF
    df-f
    biimpri
    sylan2
    3adant2
    pm4.71i
    @8
    @12
    ancom
    3bitr4ri
    bitri
    bitri
    bitri
end
