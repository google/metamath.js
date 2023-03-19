include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "cdm.mm"
include "wi.mm"
include "cca.mm"
include "wral.mm"
include "wb.mm"
include "wtru.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cme.mm"
include "a1i.mm"
include "iscmet3.mm"
include "trud.mm"
include "ex.mm"
include "mprgbir.mm"

theorem iscmet3i
  let cD: class D
  let vf: setvar f
  let cJ: class J
  let cX: class X
  assume iscmet3i.2: |- J = ( MetOpen ` D )
  assume iscmet3i.3: |- D e. ( Met ` X )
  assume iscmet3i.4: |- ( ( f e. ( Cau ` D ) /\ f : NN --> X ) -> f e. dom ( ~~>t ` J ) )

  disjoint D f
  disjoint J f
  disjoint X f
  assert |- D e. ( CMet ` X )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cn
    cX
    vf
    cv
    #
    wf
    #
    @1
    cJ
    clm
    cfv
    cdm
    wcel
    #
    wi
    #
    vf
    cD
    cca
    cfv
    #
    @0
    @4
    vf
    @5
    wral
    wb
    wtru
    cD
    vf
    cJ
    c1
    cX
    cn
    nnuz
    iscmet3i.2
    wtru
    1zzd
    cD
    cX
    cme
    cfv
    wcel
    wtru
    iscmet3i.3
    a1i
    iscmet3
    trud
    @1
    @5
    wcel
    @2
    @3
    iscmet3i.4
    ex
    mprgbir
end
