include "word.mm"
include "cuni.mm"
include "wceq.mm"
include "c0.mm"
include "wlim.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "wne.mm"
include "df-ne.mm"
include "w3a.mm"
include "df-lim.mm"
include "biimpri.mm"
include "3exp.mm"
include "syl5bir.mm"
include "com23.mm"
include "imp.mm"
include "orrd.mm"
include "ex.mm"
include "uni0.mm"
include "eqcomi.mm"
include "id.mm"
include "unieq.mm"
include "3eqtr4a.mm"
include "limuni.mm"
include "jaoi.mm"
include "impbid1.mm"

theorem unizlim
  let cA: class A


  assert |- ( Ord A -> ( A = U. A <-> ( A = (/) \/ Lim A ) ) )

  proof
    cA
    word
    #
    cA
    cA
    cuni
    #
    wceq
    #
    cA
    c0
    wceq
    #
    cA
    wlim
    #
    wo
    #
    @0
    @2
    @5
    @0
    @2
    wa
    @3
    @4
    @0
    @2
    @3
    wn
    #
    @4
    wi
    @0
    @6
    @2
    @4
    @6
    cA
    c0
    wne
    #
    @0
    @2
    @4
    wi
    cA
    c0
    df-ne
    @0
    @7
    @2
    @4
    @4
    @0
    @7
    @2
    w3a
    cA
    df-lim
    biimpri
    3exp
    syl5bir
    com23
    imp
    orrd
    ex
    @3
    @2
    @4
    @3
    c0
    c0
    cuni
    #
    cA
    @1
    @8
    c0
    uni0
    eqcomi
    @3
    id
    cA
    c0
    unieq
    3eqtr4a
    cA
    limuni
    jaoi
    impbid1
end
