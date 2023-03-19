include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "ctop.mm"
include "ckgen.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-kgen.mm"
include "a1i.mm"
include "wa.mm"
include "unieq.mm"
include "toponuni.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "pweqd.mm"
include "wb.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "eleq2d.mm"
include "imbi12d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "topontop.mm"
include "toponmax.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "fvmptd.mm"

theorem kgenval
  let vx: setvar x
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let cA: class A
  let vj: setvar j

  disjoint k x
  disjoint J k
  disjoint J x
  disjoint X k
  disjoint X x
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint J j
  disjoint X j
  assert |- ( J e. ( TopOn ` X ) -> ( kGen ` J ) = { x e. ~P X | A. k e. ~P X ( ( J |`t k ) e. Comp -> ( x i^i k ) e. ( J |`t k ) ) } )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    vj
    cJ
    vj
    cv
    #
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    cv
    @2
    cin
    #
    @3
    wcel
    #
    wi
    #
    vk
    @1
    cuni
    #
    cpw
    #
    wral
    #
    vx
    @9
    crab
    #
    cJ
    @2
    crest
    co
    #
    ccmp
    wcel
    #
    @5
    @12
    wcel
    #
    wi
    #
    vk
    cX
    cpw
    #
    wral
    #
    vx
    @16
    crab
    #
    ctop
    ckgen
    cvv
    ckgen
    vj
    ctop
    @11
    cmpt
    wceq
    @0
    vx
    vj
    vk
    df-kgen
    a1i
    @0
    @1
    cJ
    wceq
    #
    wa
    #
    @10
    @17
    vx
    @9
    @16
    @20
    @8
    cX
    @19
    @0
    @8
    cJ
    cuni
    #
    cX
    @1
    cJ
    unieq
    @0
    cX
    @21
    cX
    cJ
    toponuni
    eqcomd
    sylan9eqr
    pweqd
    #
    @20
    @7
    @15
    vk
    @9
    @16
    @22
    @19
    @7
    @15
    wb
    @0
    @19
    @4
    @13
    @6
    @14
    @19
    @3
    @12
    ccmp
    @1
    cJ
    @2
    crest
    oveq1
    #
    eleq1d
    @19
    @3
    @12
    @5
    @23
    eleq2d
    imbi12d
    adantl
    raleqbidv
    rabeqbidv
    cX
    cJ
    topontop
    @0
    cX
    cJ
    wcel
    @16
    cvv
    wcel
    @18
    cvv
    wcel
    cX
    cJ
    toponmax
    cX
    cJ
    pwexg
    @17
    vx
    @16
    cvv
    rabexg
    3syl
    fvmptd
end
