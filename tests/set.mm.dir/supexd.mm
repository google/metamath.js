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
include "wrmo.mm"
include "wcel.mm"
include "supmo.mm"
include "rmorabex.mm"
include "uniexg.mm"
include "3syl.mm"
include "syl5eqel.mm"

theorem supexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume supmo.1: |- ( ph -> R Or A )


  assert |- ( ph -> sup ( B , A , R ) e. _V )

  proof
    wph
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
    @1
    @0
    cR
    wbr
    @1
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
    wph
    @2
    vx
    cA
    wrmo
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supmo
    @2
    vx
    cA
    rmorabex
    @3
    cvv
    uniexg
    3syl
    syl5eqel
end
