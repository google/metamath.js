include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "cvv.mm"
include "wlim.mm"
include "wa.mm"
include "w3o.mm"
include "word.mm"
include "elex.mm"
include "eloni.mm"
include "ordzsl.mm"
include "3mix1.mm"
include "adantl.mm"
include "3mix2.mm"
include "3mix3.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "syl2anc.mm"
include "0elon.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "suceloni.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "limelon.mm"
include "3jaoi.mm"
include "impbii.mm"

theorem onzsl
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. On <-> ( A = (/) \/ E. x e. On A = suc x \/ ( A e. _V /\ Lim A ) ) )

  proof
    cA
    con0
    wcel
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
    cvv
    wcel
    #
    cA
    wlim
    #
    wa
    #
    w3o
    #
    @0
    @6
    cA
    word
    #
    @9
    cA
    con0
    elex
    cA
    eloni
    @10
    @6
    @1
    @5
    @7
    w3o
    @9
    vx
    cA
    ordzsl
    @6
    @1
    @9
    @5
    @7
    @1
    @9
    @6
    @1
    @5
    @8
    3mix1
    adantl
    @5
    @9
    @6
    @5
    @1
    @8
    3mix2
    adantl
    @8
    @1
    @5
    3mix3
    3jaodan
    sylan2b
    syl2anc
    @1
    @0
    @5
    @8
    @1
    @0
    c0
    con0
    wcel
    0elon
    cA
    c0
    con0
    eleq1
    mpbiri
    @4
    @0
    vx
    con0
    @2
    con0
    wcel
    @0
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
    syl5ibrcom
    rexlimiv
    cA
    cvv
    limelon
    3jaoi
    impbii
end
