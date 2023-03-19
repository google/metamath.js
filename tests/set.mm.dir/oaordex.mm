include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wss.mm"
include "wi.mm"
include "onelss.mm"
include "adantl.mm"
include "oawordex.mm"
include "sylibd.mm"
include "oaord1.mm"
include "eleq2.mm"
include "sylan9bb.mm"
include "biimprcd.mm"
include "exp4c.mm"
include "com12.mm"
include "imp4b.mm"
include "simpr.mm"
include "a1i.mm"
include "jcad.mm"
include "expd.mm"
include "reximdvai.mm"
include "ex.mm"
include "adantr.mm"
include "mpdd.mm"
include "biimpd.mm"
include "exp31.mm"
include "com34.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "impbid.mm"

theorem oaordex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. On /\ B e. On ) -> ( A e. B <-> E. x e. On ( (/) e. x /\ ( A +o x ) = B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    c0
    vx
    cv
    #
    wcel
    #
    cA
    @4
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    vx
    con0
    wrex
    #
    @2
    @3
    @7
    vx
    con0
    wrex
    #
    @9
    @2
    @3
    cA
    cB
    wss
    #
    @10
    @1
    @3
    @11
    wi
    @0
    cB
    cA
    onelss
    adantl
    vx
    cA
    cB
    oawordex
    sylibd
    @0
    @3
    @10
    @9
    wi
    #
    wi
    @1
    @0
    @3
    @12
    @0
    @3
    wa
    #
    @7
    @8
    vx
    con0
    @13
    @4
    con0
    wcel
    #
    @7
    @8
    @13
    @14
    @7
    wa
    #
    @5
    @7
    @0
    @3
    @14
    @7
    @5
    @3
    @0
    @14
    @7
    @5
    wi
    wi
    @3
    @0
    @14
    @7
    @5
    @0
    @14
    wa
    #
    @7
    wa
    #
    @5
    @3
    @16
    @5
    cA
    @6
    wcel
    @7
    @3
    cA
    @4
    oaord1
    @6
    cB
    cA
    eleq2
    sylan9bb
    #
    biimprcd
    exp4c
    com12
    imp4b
    @15
    @7
    wi
    @13
    @14
    @7
    simpr
    a1i
    jcad
    expd
    reximdvai
    ex
    adantr
    mpdd
    @0
    @9
    @3
    wi
    @1
    @0
    @8
    @3
    vx
    con0
    @0
    @14
    @5
    @7
    @3
    @0
    @14
    @7
    @5
    @3
    @0
    @14
    @7
    @5
    @3
    wi
    @17
    @5
    @3
    @18
    biimpd
    exp31
    com34
    imp4a
    rexlimdv
    adantr
    impbid
end
