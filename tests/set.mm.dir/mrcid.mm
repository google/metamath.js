include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "mress.mm"
include "mrcval.mm"
include "syldan.mm"
include "intmin.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem mrcid
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U e. C ) -> ( F ` U ) = U )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cC
    wcel
    #
    wa
    cU
    cF
    cfv
    #
    cU
    vs
    cv
    wss
    vs
    cC
    crab
    cint
    #
    cU
    @0
    @1
    cU
    cX
    wss
    @2
    @3
    wceq
    cC
    cU
    cX
    mress
    cC
    cU
    cF
    cX
    vs
    mrcfval.f
    mrcval
    syldan
    @1
    @3
    cU
    wceq
    @0
    vs
    cU
    cC
    intmin
    adantl
    eqtrd
end
