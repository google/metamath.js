include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wse.mm"
include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "ssbrd.mm"
include "ss2rabdv.mm"
include "ssexg.mm"
include "ex.mm"
include "syl.mm"
include "ralimdv.mm"
include "df-se.mm"
include "3imtr4g.mm"

theorem sess1
  let cA: class A
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( R C_ S -> ( S Se A -> R Se A ) )

  proof
    cR
    cS
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    cS
    wbr
    #
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
    @1
    @2
    cR
    wbr
    #
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
    cA
    cS
    wse
    cA
    cR
    wse
    @0
    @5
    @8
    vx
    cA
    @0
    @7
    @4
    wss
    #
    @5
    @8
    wi
    @0
    @6
    @3
    vy
    cA
    @0
    @1
    cA
    wcel
    #
    wa
    cR
    cS
    @1
    @2
    @0
    @10
    simpl
    ssbrd
    ss2rabdv
    @9
    @5
    @8
    @7
    @4
    cvv
    ssexg
    ex
    syl
    ralimdv
    vx
    vy
    cA
    cS
    df-se
    vx
    vy
    cA
    cR
    df-se
    3imtr4g
end
