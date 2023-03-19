include "wcel.mm"
include "cmre.mm"
include "cfv.mm"
include "csn.mm"
include "wss.mm"
include "snssi.mm"
include "mrccl.mm"
include "sylan2.mm"

theorem mrcsncl
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U e. X ) -> ( F ` { U } ) e. C )

  proof
    cU
    cX
    wcel
    cC
    cX
    cmre
    cfv
    wcel
    cU
    csn
    #
    cX
    wss
    @0
    cF
    cfv
    cC
    wcel
    cU
    cX
    snssi
    cC
    @0
    cF
    cX
    mrcfval.f
    mrccl
    sylan2
end
