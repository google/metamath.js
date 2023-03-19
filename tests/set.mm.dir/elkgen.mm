include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckgen.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "kgenval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "wb.mm"
include "toponmax.mm"
include "elpw2g.mm"
include "syl.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem elkgen
  let cA: class A
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vj: setvar j

  disjoint A k
  disjoint J k
  disjoint X k
  disjoint k x
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint J j
  disjoint J x
  disjoint X j
  disjoint X x
  assert |- ( J e. ( TopOn ` X ) -> ( A e. ( kGen ` J ) <-> ( A C_ X /\ A. k e. ~P X ( ( J |`t k ) e. Comp -> ( A i^i k ) e. ( J |`t k ) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cJ
    ckgen
    cfv
    #
    wcel
    cA
    cJ
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
    #
    @2
    cin
    #
    @3
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
    @9
    crab
    #
    wcel
    #
    cA
    cX
    wss
    #
    @4
    cA
    @2
    cin
    #
    @3
    wcel
    #
    wi
    #
    vk
    @9
    wral
    #
    wa
    #
    @0
    @1
    @11
    cA
    vx
    vk
    cJ
    cX
    kgenval
    eleq2d
    @12
    cA
    @9
    wcel
    #
    @17
    wa
    @0
    @18
    @10
    @17
    vx
    cA
    @9
    @5
    cA
    wceq
    #
    @8
    @16
    vk
    @9
    @20
    @7
    @15
    @4
    @20
    @6
    @14
    @3
    @5
    cA
    @2
    ineq1
    eleq1d
    imbi2d
    ralbidv
    elrab
    @0
    @19
    @13
    @17
    @0
    cX
    cJ
    wcel
    @19
    @13
    wb
    cX
    cJ
    toponmax
    cA
    cX
    cJ
    elpw2g
    syl
    anbi1d
    syl5bb
    bitrd
end
