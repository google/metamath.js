include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "csn.mm"
include "ciun.mm"
include "cvv.mm"
include "iunid.mm"
include "xpeq2i.mm"
include "xpiundi.mm"
include "eqtr3i.mm"
include "wral.mm"
include "id.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "mptexg.mm"
include "syl5eqel.mm"
include "ralrimivw.mm"
include "iunexg.mm"
include "syl2anr.mm"

theorem xpexgALT
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cA
    cB
    cxp
    #
    vy
    cB
    cA
    vy
    cv
    #
    csn
    #
    cxp
    #
    ciun
    #
    cvv
    cA
    vy
    cB
    @4
    ciun
    #
    cxp
    @2
    @6
    @7
    cB
    cA
    vy
    cB
    iunid
    xpeq2i
    vy
    cB
    @4
    cA
    xpiundi
    eqtr3i
    @1
    @1
    @5
    cvv
    wcel
    #
    vy
    cB
    wral
    @6
    cvv
    wcel
    @0
    @1
    id
    @0
    @8
    vy
    cB
    @0
    @5
    vx
    cA
    @3
    cmpt
    cvv
    vx
    cA
    @3
    fconstmpt
    vx
    cA
    @3
    cV
    mptexg
    syl5eqel
    ralrimivw
    vy
    cB
    @5
    cW
    cvv
    iunexg
    syl2anr
    syl5eqel
end
