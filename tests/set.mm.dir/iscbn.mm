include "cv.mm"
include "cims.mm"
include "cfv.mm"
include "cba.mm"
include "cms.mm"
include "wcel.mm"
include "cnv.mm"
include "ccbn.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "df-cbn.mm"
include "elrab2.mm"

theorem iscbn
  let cD: class D
  let cU: class U
  let cX: class X
  let vu: setvar u
  assume iscbn.x: |- X = ( BaseSet ` U )
  assume iscbn.8: |- D = ( IndMet ` U )


  assert |- ( U e. CBan <-> ( U e. NrmCVec /\ D e. ( CMet ` X ) ) )

  proof
    vu
    cv
    #
    cims
    cfv
    #
    @0
    cba
    cfv
    #
    cms
    cfv
    #
    wcel
    cD
    cX
    cms
    cfv
    #
    wcel
    vu
    cU
    cnv
    ccbn
    @0
    cU
    wceq
    #
    @1
    cD
    @3
    @4
    @5
    @1
    cU
    cims
    cfv
    cD
    @0
    cU
    cims
    fveq2
    iscbn.8
    syl6eqr
    @5
    @2
    cX
    cms
    @5
    @2
    cU
    cba
    cfv
    cX
    @0
    cU
    cba
    fveq2
    iscbn.x
    syl6eqr
    fveq2d
    eleq12d
    vu
    df-cbn
    elrab2
end
