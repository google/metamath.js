include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "mrcid.mm"
include "wa.mm"
include "simpr.mm"
include "wss.mm"
include "mrcssv.mm"
include "adantr.mm"
include "eqsstr3d.mm"
include "mrccl.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "impbida.mm"

theorem mrcidb
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( C e. ( Moore ` X ) -> ( U e. C <-> ( F ` U ) = U ) )

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
    cU
    cF
    cfv
    #
    cU
    wceq
    #
    cC
    cU
    cF
    cX
    mrcfval.f
    mrcid
    @0
    @2
    wa
    #
    @1
    cU
    cC
    @0
    @2
    simpr
    #
    @0
    @2
    cU
    cX
    wss
    @1
    cC
    wcel
    @3
    cU
    @1
    cX
    @4
    @0
    @1
    cX
    wss
    @2
    cC
    cU
    cF
    cX
    mrcfval.f
    mrcssv
    adantr
    eqsstr3d
    cC
    cU
    cF
    cX
    mrcfval.f
    mrccl
    syldan
    eqeltrrd
    impbida
end
