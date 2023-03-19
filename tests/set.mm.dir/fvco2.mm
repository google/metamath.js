include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "ccom.mm"
include "csn.mm"
include "cima.mm"
include "cio.mm"
include "cfv.mm"
include "fnsnfv.mm"
include "imaeq2d.mm"
include "imaco.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "iotabidv.mm"
include "dffv3.mm"
include "3eqtr4g.mm"

theorem fvco2
  let cA: class A
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( G Fn A /\ X e. A ) -> ( ( F o. G ) ` X ) = ( F ` ( G ` X ) ) )

  proof
    cG
    cA
    wfn
    cX
    cA
    wcel
    wa
    #
    vx
    cv
    #
    cF
    cG
    ccom
    #
    cX
    csn
    #
    cima
    #
    wcel
    #
    vx
    cio
    @1
    cF
    cX
    cG
    cfv
    #
    csn
    #
    cima
    #
    wcel
    #
    vx
    cio
    cX
    @2
    cfv
    @6
    cF
    cfv
    @0
    @5
    @9
    vx
    @0
    @4
    @8
    @1
    @0
    @8
    cF
    cG
    @3
    cima
    #
    cima
    @4
    @0
    @7
    @10
    cF
    cA
    cX
    cG
    fnsnfv
    imaeq2d
    cF
    cG
    @3
    imaco
    syl6reqr
    eleq2d
    iotabidv
    vx
    cX
    @2
    dffv3
    vx
    @6
    cF
    dffv3
    3eqtr4g
end
