include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "cuni.mm"
include "fvssunirn.mm"
include "cpw.mm"
include "wf.mm"
include "wss.mm"
include "mrcf.mm"
include "frn.mm"
include "uniss.mm"
include "3syl.mm"
include "mreuni.mm"
include "sseqtrd.mm"
include "syl5ss.mm"

theorem mrcssv
  let cC: class C
  let cU: class U
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let cV: class V
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( C e. ( Moore ` X ) -> ( F ` U ) C_ X )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cF
    cfv
    cF
    crn
    #
    cuni
    #
    cX
    cF
    cU
    fvssunirn
    @0
    @2
    cC
    cuni
    #
    cX
    @0
    cX
    cpw
    #
    cC
    cF
    wf
    @1
    cC
    wss
    @2
    @3
    wss
    cC
    cF
    cX
    mrcfval.f
    mrcf
    @4
    cC
    cF
    frn
    @1
    cC
    uniss
    3syl
    cC
    cX
    mreuni
    sseqtrd
    syl5ss
end
