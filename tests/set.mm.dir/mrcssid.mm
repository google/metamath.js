include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "ssintub.mm"
include "mrcval.mm"
include "syl5sseqr.mm"

theorem mrcssid
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> U C_ ( F ` U ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    cU
    cX
    wss
    wa
    cU
    vs
    cv
    wss
    vs
    cC
    crab
    cint
    cU
    cU
    cF
    cfv
    vs
    cU
    cC
    ssintub
    cC
    cU
    cF
    cX
    vs
    mrcfval.f
    mrcval
    syl5sseqr
end
