include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "wf.mm"
include "mrcf.mm"
include "adantr.mm"
include "wb.mm"
include "mre1cl.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "ffvelrnd.mm"

theorem mrccl
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ X ) -> ( F ` U ) e. C )

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
    cX
    cpw
    #
    cC
    cU
    cF
    @0
    @2
    cC
    cF
    wf
    @1
    cC
    cF
    cX
    mrcfval.f
    mrcf
    adantr
    @0
    cU
    @2
    wcel
    #
    @1
    @0
    cX
    cC
    wcel
    @3
    @1
    wb
    cC
    cX
    mre1cl
    cU
    cX
    cC
    elpw2g
    syl
    biimpar
    ffvelrnd
end
