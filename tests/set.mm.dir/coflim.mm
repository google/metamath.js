include "wlim.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "eleq2.mm"
include "biimprd.mm"
include "wel.mm"
include "eluni2.mm"
include "con0.mm"
include "wi.mm"
include "word.mm"
include "limord.mm"
include "ssel2.mm"
include "ordelon.mm"
include "syl2an.mm"
include "expr.mm"
include "onelss.mm"
include "syl6.mm"
include "reximdvai.mm"
include "syl5bi.mm"
include "syl9r.mm"
include "ralrimdv.mm"
include "w3a.mm"
include "uniss.mm"
include "3ad2ant2.mm"
include "uniss2.mm"
include "3ad2ant3.mm"
include "eqssd.mm"
include "limuni.mm"
include "3ad2ant1.mm"
include "eqtr4d.mm"
include "3expia.mm"
include "impbid.mm"

theorem coflim
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ( Lim A /\ B C_ A ) -> ( U. B = A <-> A. x e. A E. y e. B x C_ y ) )

  proof
    cA
    wlim
    #
    cB
    cA
    wss
    #
    wa
    #
    cB
    cuni
    #
    cA
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @2
    @4
    @8
    vx
    cA
    @4
    @5
    cA
    wcel
    #
    @5
    @3
    wcel
    #
    @2
    @8
    @4
    @11
    @10
    @3
    cA
    @5
    eleq2
    biimprd
    @11
    vx
    vy
    wel
    #
    vy
    cB
    wrex
    @2
    @8
    vy
    @5
    cB
    eluni2
    @2
    @12
    @7
    vy
    cB
    @2
    @6
    cB
    wcel
    #
    @6
    con0
    wcel
    #
    @12
    @7
    wi
    @0
    @1
    @13
    @14
    @0
    cA
    word
    @6
    cA
    wcel
    @14
    @1
    @13
    wa
    cA
    limord
    cB
    cA
    @6
    ssel2
    cA
    @6
    ordelon
    syl2an
    expr
    @6
    @5
    onelss
    syl6
    reximdvai
    syl5bi
    syl9r
    ralrimdv
    @0
    @1
    @9
    @4
    @0
    @1
    @9
    w3a
    #
    @3
    cA
    cuni
    #
    cA
    @15
    @3
    @16
    @1
    @0
    @3
    @16
    wss
    @9
    cB
    cA
    uniss
    3ad2ant2
    @9
    @0
    @16
    @3
    wss
    @1
    vx
    vy
    cA
    cB
    uniss2
    3ad2ant3
    eqssd
    @0
    @1
    cA
    @16
    wceq
    @9
    cA
    limuni
    3ad2ant1
    eqtr4d
    3expia
    impbid
end
