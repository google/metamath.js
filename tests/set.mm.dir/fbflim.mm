include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "wa.mm"
include "cflim.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "wrex.mm"
include "cfil.mm"
include "wb.mm"
include "cfg.mm"
include "fgcl.mm"
include "syl5eqel.mm"
include "flimopn.mm"
include "sylan2.mm"
include "eleq2i.mm"
include "elfg.mm"
include "ad3antlr.mm"
include "syl5bb.mm"
include "simpll.mm"
include "toponss.mm"
include "sylan.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem fbflim
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cX: class X
  let vn: setvar n
  assume fbflim.3: |- F = ( X filGen B )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint F x
  disjoint F y
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint B n
  disjoint J n
  disjoint X n
  assert |- ( ( J e. ( TopOn ` X ) /\ B e. ( fBas ` X ) ) -> ( A e. ( J fLim F ) <-> ( A e. X /\ A. x e. J ( A e. x -> E. y e. B y C_ x ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cB
    cX
    cfbas
    cfv
    wcel
    #
    wa
    #
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    vx
    cv
    #
    wcel
    #
    @5
    cF
    wcel
    #
    wi
    #
    vx
    cJ
    wral
    #
    wa
    #
    @4
    @6
    vy
    cv
    @5
    wss
    vy
    cB
    wrex
    #
    wi
    #
    vx
    cJ
    wral
    #
    wa
    @1
    @0
    cF
    cX
    cfil
    cfv
    #
    wcel
    @3
    @10
    wb
    @1
    cF
    cX
    cB
    cfg
    co
    #
    @14
    fbflim.3
    cB
    cX
    fgcl
    syl5eqel
    vx
    cA
    cF
    cJ
    cX
    flimopn
    sylan2
    @2
    @4
    @9
    @13
    @2
    @4
    wa
    #
    @8
    @12
    vx
    cJ
    @16
    @5
    cJ
    wcel
    #
    wa
    #
    @7
    @11
    @6
    @18
    @7
    @5
    cX
    wss
    #
    @11
    wa
    #
    @11
    @7
    @5
    @15
    wcel
    #
    @18
    @20
    cF
    @15
    @5
    fbflim.3
    eleq2i
    @1
    @21
    @20
    wb
    @0
    @4
    @17
    vy
    @5
    cB
    cX
    elfg
    ad3antlr
    syl5bb
    @18
    @19
    @11
    @16
    @0
    @17
    @19
    @0
    @1
    @4
    simpll
    @5
    cJ
    cX
    toponss
    sylan
    biantrurd
    bitr4d
    imbi2d
    ralbidva
    pm5.32da
    bitrd
end
