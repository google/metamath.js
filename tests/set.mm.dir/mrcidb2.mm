include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "mrcidb.mm"
include "adantr.mm"
include "mrcssid.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "bitrd.mm"

theorem mrcidb2
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> ( U e. C <-> ( F ` U ) C_ U ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cX
    wss
    #
    wa
    #
    cU
    cC
    wcel
    #
    cU
    cF
    cfv
    #
    cU
    wceq
    #
    @4
    cU
    wss
    #
    @0
    @3
    @5
    wb
    @1
    cC
    cU
    cF
    cX
    mrcfval.f
    mrcidb
    adantr
    @2
    @6
    @6
    cU
    @4
    wss
    #
    wa
    @5
    @2
    @7
    @6
    cC
    cU
    cF
    cX
    mrcfval.f
    mrcssid
    biantrud
    @4
    cU
    eqss
    syl6rbbr
    bitrd
end
