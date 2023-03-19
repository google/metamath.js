include "wcel.mm"
include "csup.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "cuni.mm"
include "cvv.mm"
include "df-sup.mm"
include "rabexg.mm"
include "uniexg.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem supex2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. C -> sup ( B , A , R ) e. _V )

  proof
    cA
    cC
    wcel
    #
    cB
    cA
    cR
    csup
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    @2
    @1
    cR
    wbr
    @2
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    wi
    vy
    cA
    wral
    wa
    #
    vx
    cA
    crab
    #
    cuni
    #
    cvv
    vx
    vy
    vz
    cB
    cA
    cR
    df-sup
    @0
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    @3
    vx
    cA
    cC
    rabexg
    @4
    cvv
    uniexg
    syl
    syl5eqel
end
