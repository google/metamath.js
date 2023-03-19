include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "cab.mm"
include "cvv.mm"
include "ancom.mm"
include "abbii.mm"
include "xpexg.mm"
include "abssexg.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem pmex
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f

  disjoint A f
  disjoint B f
  assert |- ( ( A e. C /\ B e. D ) -> { f | ( Fun f /\ f C_ ( A X. B ) ) } e. _V )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    vf
    cv
    #
    wfun
    #
    @1
    cA
    cB
    cxp
    #
    wss
    #
    wa
    #
    vf
    cab
    @4
    @2
    wa
    #
    vf
    cab
    #
    cvv
    @5
    @6
    vf
    @2
    @4
    ancom
    abbii
    @0
    @3
    cvv
    wcel
    @7
    cvv
    wcel
    cA
    cB
    cC
    cD
    xpexg
    @2
    vf
    @3
    cvv
    abssexg
    syl
    syl5eqel
end
