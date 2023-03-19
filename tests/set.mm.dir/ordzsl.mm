include "word.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "wlim.mm"
include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "cuni.mm"
include "orduninsuc.mm"
include "biimprd.mm"
include "unizlim.mm"
include "sylibd.mm"
include "orrd.mm"
include "3orass.mm"
include "or12.mm"
include "bitri.mm"
include "sylibr.mm"
include "ord0.mm"
include "ordeq.mm"
include "mpbiri.mm"
include "wcel.mm"
include "suceloni.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "eloni.mm"
include "syl6com.mm"
include "rexlimiv.mm"
include "limord.mm"
include "3jaoi.mm"
include "impbii.mm"

theorem ordzsl
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( Ord A <-> ( A = (/) \/ E. x e. On A = suc x \/ Lim A ) )

  proof
    cA
    word
    #
    cA
    c0
    wceq
    #
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    cA
    wlim
    #
    w3o
    #
    @0
    @5
    @1
    @6
    wo
    #
    wo
    #
    @7
    @0
    @5
    @8
    @0
    @5
    wn
    #
    cA
    cA
    cuni
    wceq
    #
    @8
    @0
    @11
    @10
    vx
    cA
    orduninsuc
    biimprd
    cA
    unizlim
    sylibd
    orrd
    @7
    @1
    @5
    @6
    wo
    wo
    @9
    @1
    @5
    @6
    3orass
    @1
    @5
    @6
    or12
    bitri
    sylibr
    @1
    @0
    @5
    @6
    @1
    @0
    c0
    word
    ord0
    cA
    c0
    ordeq
    mpbiri
    @4
    @0
    vx
    con0
    @4
    @2
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    @0
    @12
    @13
    @4
    @3
    con0
    wcel
    @2
    suceloni
    cA
    @3
    con0
    eleq1
    syl5ibr
    cA
    eloni
    syl6com
    rexlimiv
    cA
    limord
    3jaoi
    impbii
end
