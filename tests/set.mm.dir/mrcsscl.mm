include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "mress.mm"
include "3adant2.mm"
include "mrcss.mm"
include "syld3an3.mm"
include "wceq.mm"
include "mrcid.mm"
include "sseqtrd.mm"

theorem mrcsscl
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ V /\ V e. C ) -> ( F ` U ) C_ V )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cV
    wss
    #
    cV
    cC
    wcel
    #
    w3a
    cU
    cF
    cfv
    #
    cV
    cF
    cfv
    #
    cV
    @0
    @1
    @2
    cV
    cX
    wss
    #
    @3
    @4
    wss
    @0
    @2
    @5
    @1
    cC
    cV
    cX
    mress
    3adant2
    cC
    cU
    cF
    cV
    cX
    mrcfval.f
    mrcss
    syld3an3
    @0
    @2
    @4
    cV
    wceq
    @1
    cC
    cV
    cF
    cX
    mrcfval.f
    mrcid
    3adant2
    sseqtrd
end
