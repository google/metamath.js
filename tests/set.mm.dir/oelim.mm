include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "con0.mm"
include "c0.mm"
include "coe.mm"
include "co.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "limelon.mm"
include "simpr.mm"
include "jca.mm"
include "cvv.mm"
include "comu.mm"
include "cmpt.mm"
include "c1o.mm"
include "crdg.mm"
include "cfv.mm"
include "rdglim2a.mm"
include "ad2antlr.mm"
include "wb.mm"
include "oevn0.mm"
include "onelon.mm"
include "sylanl2.mm"
include "exp42.mm"
include "com34.mm"
include "imp41.mm"
include "iuneq2dv.mm"
include "eqeq12d.mm"
include "adantlrr.mm"
include "mpbird.mm"

theorem oelim
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  assert |- ( ( ( A e. On /\ ( B e. C /\ Lim B ) ) /\ (/) e. A ) -> ( A ^o B ) = U_ x e. B ( A ^o x ) )

  proof
    cB
    cC
    wcel
    #
    cB
    wlim
    #
    wa
    #
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    @1
    wa
    #
    c0
    cA
    wcel
    #
    cA
    cB
    coe
    co
    #
    vx
    cB
    cA
    vx
    cv
    #
    coe
    co
    #
    ciun
    #
    wceq
    #
    @2
    @4
    @1
    cB
    cC
    limelon
    @0
    @1
    simpr
    jca
    @3
    @5
    wa
    @6
    wa
    @11
    cB
    vy
    cvv
    vy
    cv
    cA
    comu
    co
    cmpt
    #
    c1o
    crdg
    #
    cfv
    #
    vx
    cB
    @8
    @13
    cfv
    #
    ciun
    #
    wceq
    #
    @5
    @17
    @3
    @6
    vx
    c1o
    cB
    con0
    @12
    rdglim2a
    ad2antlr
    @3
    @4
    @6
    @11
    @17
    wb
    @1
    @3
    @4
    wa
    @6
    wa
    #
    @7
    @14
    @10
    @16
    vy
    cA
    cB
    oevn0
    @18
    vx
    cB
    @9
    @15
    @3
    @4
    @6
    @8
    cB
    wcel
    #
    @9
    @15
    wceq
    #
    @3
    @4
    @19
    @6
    @20
    @3
    @4
    @19
    @6
    @20
    @4
    @19
    wa
    @3
    @8
    con0
    wcel
    @6
    @20
    cB
    @8
    onelon
    vy
    cA
    @8
    oevn0
    sylanl2
    exp42
    com34
    imp41
    iuneq2dv
    eqeq12d
    adantlrr
    mpbird
    sylanl2
end
