include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "mrcflem.mm"
include "mrcfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem mrcf
  let cC: class C
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cU: class U
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( C e. ( Moore ` X ) -> F : ~P X --> C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cX
    cpw
    #
    cC
    cF
    wf
    @1
    cC
    vx
    @1
    vx
    cv
    vs
    cv
    wss
    vs
    cC
    crab
    cint
    cmpt
    #
    wf
    vx
    cC
    cX
    vs
    mrcflem
    @0
    @1
    cC
    cF
    @2
    vx
    cC
    cF
    cX
    vs
    mrcfval.f
    mrcfval
    feq1d
    mpbird
end
