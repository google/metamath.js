include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "cmnf.mm"
include "wn.mm"
include "wa.mm"
include "cxr.mm"
include "wne.mm"
include "pm5.61.mm"
include "w3o.mm"
include "elxr.mm"
include "df-3or.mm"
include "bitri.mm"
include "df-ne.mm"
include "anbi12i.mm"
include "renemnf.mm"
include "pnfnemnf.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "neneqd.mm"
include "pm4.71i.mm"
include "3bitr4i.mm"

theorem xrnemnf
  let cA: class A


  assert |- ( ( A e. RR* /\ A =/= -oo ) <-> ( A e. RR \/ A = +oo ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    wo
    #
    cA
    cmnf
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
    cmnf
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
    @1
    @3
    w3o
    @4
    cA
    elxr
    @0
    @1
    @3
    df-3or
    bitri
    cA
    cmnf
    df-ne
    anbi12i
    @2
    @5
    @2
    cA
    cmnf
    @0
    @7
    @1
    cA
    renemnf
    @1
    @7
    cpnf
    cmnf
    wne
    pnfnemnf
    cA
    cpnf
    cmnf
    neeq1
    mpbiri
    jaoi
    neneqd
    pm4.71i
    3bitr4i
end
