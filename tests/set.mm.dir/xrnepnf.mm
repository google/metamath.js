include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wceq.mm"
include "wo.mm"
include "cpnf.mm"
include "wn.mm"
include "wa.mm"
include "cxr.mm"
include "wne.mm"
include "pm5.61.mm"
include "w3o.mm"
include "elxr.mm"
include "df-3or.mm"
include "or32.mm"
include "3bitri.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "renepnf.mm"
include "mnfnepnf.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "neneqd.mm"
include "pm4.71i.mm"
include "3bitr4i.mm"

theorem xrnepnf
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= +oo ) <-> ( A e. RR \/ A = -oo ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cmnf
    wceq
    #
    wo
    #
    cA
    cpnf
    wceq
    #
    wo
    #
    @3
    wn
    #
    wa
    @2
    @5
    wa
    cA
    cxr
    wcel
    #
    cA
    cpnf
    wne
    #
    wa
    @2
    @2
    @3
    pm5.61
    @6
    @4
    @7
    @5
    @6
    @0
    @3
    @1
    w3o
    @0
    @3
    wo
    @1
    wo
    @4
    cA
    elxr
    @0
    @3
    @1
    df-3or
    @0
    @3
    @1
    or32
    3bitri
    cA
    cpnf
    df-ne
    anbi12i
    @2
    @5
    @2
    cA
    cpnf
    @0
    @7
    @1
    cA
    renepnf
    @1
    @7
    cmnf
    cpnf
    wne
    mnfnepnf
    cA
    cmnf
    cpnf
    neeq1
    mpbiri
    jaoi
    neneqd
    pm4.71i
    3bitr4i
end
