include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wse.mm"
include "ssralv.mm"
include "wi.mm"
include "rabss2.mm"
include "ssexg.mm"
include "ex.mm"
include "syl.mm"
include "ralimdv.mm"
include "syld.mm"
include "df-se.mm"
include "3imtr4g.mm"

theorem sess2
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S


  assert |- ( A C_ B -> ( R Se B -> R Se A ) )

  proof
    cA
    cB
    wss
    #
    vy
    cv
    vx
    cv
    cR
    wbr
    #
    vy
    cB
    crab
    #
    cvv
    wcel
    #
    vx
    cB
    wral
    #
    @1
    vy
    cA
    crab
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    cB
    cR
    wse
    cA
    cR
    wse
    @0
    @4
    @3
    vx
    cA
    wral
    @7
    @3
    vx
    cA
    cB
    ssralv
    @0
    @3
    @6
    vx
    cA
    @0
    @5
    @2
    wss
    #
    @3
    @6
    wi
    @1
    vy
    cA
    cB
    rabss2
    @8
    @3
    @6
    @5
    @2
    cvv
    ssexg
    ex
    syl
    ralimdv
    syld
    vx
    vy
    cB
    cR
    df-se
    vx
    vy
    cA
    cR
    df-se
    3imtr4g
end
