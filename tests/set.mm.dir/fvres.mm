include "wcel.mm"
include "cv.mm"
include "cres.mm"
include "wbr.mm"
include "cio.mm"
include "cfv.mm"
include "vex.mm"
include "brres.mm"
include "rbaib.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "3eqtr4g.mm"

theorem fvres
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( A e. B -> ( ( F |` B ) ` A ) = ( F ` A ) )

  proof
    cA
    cB
    wcel
    #
    cA
    vx
    cv
    #
    cF
    cB
    cres
    #
    wbr
    #
    vx
    cio
    cA
    @1
    cF
    wbr
    #
    vx
    cio
    cA
    @2
    cfv
    cA
    cF
    cfv
    @0
    @3
    @4
    vx
    @3
    @4
    @0
    cA
    @1
    cF
    cB
    vx
    vex
    brres
    rbaib
    iotabidv
    vx
    cA
    @2
    df-fv
    vx
    cA
    cF
    df-fv
    3eqtr4g
end
