include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "cfv.mm"
include "breq.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "3eqtr4g.mm"

theorem fveq1
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x
  let cB: class B


  assert |- ( F = G -> ( F ` A ) = ( G ` A ) )

  proof
    cF
    cG
    wceq
    #
    cA
    vx
    cv
    #
    cF
    wbr
    #
    vx
    cio
    cA
    @1
    cG
    wbr
    #
    vx
    cio
    cA
    cF
    cfv
    cA
    cG
    cfv
    @0
    @2
    @3
    vx
    cA
    @1
    cF
    cG
    breq
    iotabidv
    vx
    cA
    cF
    df-fv
    vx
    cA
    cG
    df-fv
    3eqtr4g
end
