include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "cfv.mm"
include "breq1.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "3eqtr4g.mm"

theorem fveq2
  param cA: class A
  param cB: class B
  param cF: class F
  let vx: setvar x
  let cG: class G


  assert |- ( A = B -> ( F ` A ) = ( F ` B ) )

  proof
    cA
    cB
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
    cB
    @1
    cF
    wbr
    #
    vx
    cio
    cA
    cF
    cfv
    cB
    cF
    cfv
    @0
    @2
    @3
    vx
    cA
    cB
    @1
    cF
    breq1
    iotabidv
    vx
    cA
    cF
    df-fv
    vx
    cB
    cF
    df-fv
    3eqtr4g
end
