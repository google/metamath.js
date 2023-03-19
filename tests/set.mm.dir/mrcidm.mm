include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "mrccl.mm"
include "mrcid.mm"
include "syldan.mm"

theorem mrcidm
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> ( F ` ( F ` U ) ) = ( F ` U ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    cU
    cX
    wss
    cU
    cF
    cfv
    #
    cC
    wcel
    @0
    cF
    cfv
    @0
    wceq
    cC
    cU
    cF
    cX
    mrcfval.f
    mrccl
    cC
    @0
    cF
    cX
    mrcfval.f
    mrcid
    syldan
end
