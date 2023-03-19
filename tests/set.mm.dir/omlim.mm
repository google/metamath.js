include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "con0.mm"
include "comu.mm"
include "co.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "limelon.mm"
include "simpr.mm"
include "jca.mm"
include "cvv.mm"
include "coa.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "rdglim2a.mm"
include "adantl.mm"
include "wb.mm"
include "omv.mm"
include "onelon.mm"
include "sylan2.mm"
include "anassrs.mm"
include "iuneq2dv.mm"
include "eqeq12d.mm"
include "adantrr.mm"
include "mpbird.mm"

theorem omlim
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  assert |- ( ( A e. On /\ ( B e. C /\ Lim B ) ) -> ( A .o B ) = U_ x e. B ( A .o x ) )

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
    cA
    cB
    comu
    co
    #
    vx
    cB
    cA
    vx
    cv
    #
    comu
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
    @10
    cB
    vy
    cvv
    vy
    cv
    cA
    coa
    co
    cmpt
    #
    c0
    crdg
    #
    cfv
    #
    vx
    cB
    @7
    @12
    cfv
    #
    ciun
    #
    wceq
    #
    @5
    @16
    @3
    vx
    c0
    cB
    con0
    @11
    rdglim2a
    adantl
    @3
    @4
    @10
    @16
    wb
    @1
    @3
    @4
    wa
    #
    @6
    @13
    @9
    @15
    vy
    cA
    cB
    omv
    @17
    vx
    cB
    @8
    @14
    @3
    @4
    @7
    cB
    wcel
    #
    @8
    @14
    wceq
    #
    @4
    @18
    wa
    @3
    @7
    con0
    wcel
    @19
    cB
    @7
    onelon
    vy
    cA
    @7
    omv
    sylan2
    anassrs
    iuneq2dv
    eqeq12d
    adantrr
    mpbird
    sylan2
end
