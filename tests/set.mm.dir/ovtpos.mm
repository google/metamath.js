include "cop.mm"
include "ctpos.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "brtpos.mm"
include "ax-mp.mm"
include "iotabii.mm"
include "df-fv.mm"
include "3eqtr4i.mm"
include "df-ov.mm"

theorem ovtpos
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( A tpos F B ) = ( B F A )

  proof
    cA
    cB
    cop
    #
    cF
    ctpos
    #
    cfv
    #
    cB
    cA
    cop
    #
    cF
    cfv
    #
    cA
    cB
    @1
    co
    cB
    cA
    cF
    co
    @0
    vy
    cv
    #
    @1
    wbr
    #
    vy
    cio
    @3
    @5
    cF
    wbr
    #
    vy
    cio
    @2
    @4
    @6
    @7
    vy
    @5
    cvv
    wcel
    @6
    @7
    wb
    vy
    vex
    cA
    cB
    @5
    cF
    cvv
    brtpos
    ax-mp
    iotabii
    vy
    @0
    @1
    df-fv
    vy
    @3
    cF
    df-fv
    3eqtr4i
    cA
    cB
    @1
    df-ov
    cB
    cA
    cF
    df-ov
    3eqtr4i
end
