include "cnv.mm"
include "wcel.mm"
include "cims.mm"
include "cfv.mm"
include "cnmcv.mm"
include "cnsb.mm"
include "ccom.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2.mm"
include "coeq12d.mm"
include "df-ims.mm"
include "fvex.mm"
include "coex.mm"
include "fvmpt.mm"
include "coeq12i.mm"
include "3eqtr4g.mm"

theorem imsval
  let cD: class D
  let cU: class U
  let cM: class M
  let cN: class N
  let vu: setvar u
  assume imsval.3: |- M = ( -v ` U )
  assume imsval.6: |- N = ( normCV ` U )
  assume imsval.8: |- D = ( IndMet ` U )


  assert |- ( U e. NrmCVec -> D = ( N o. M ) )

  proof
    cU
    cnv
    wcel
    cU
    cims
    cfv
    cU
    cnmcv
    cfv
    #
    cU
    cnsb
    cfv
    #
    ccom
    #
    cD
    cN
    cM
    ccom
    vu
    cU
    vu
    cv
    #
    cnmcv
    cfv
    #
    @3
    cnsb
    cfv
    #
    ccom
    @2
    cnv
    cims
    @3
    cU
    wceq
    @4
    @0
    @5
    @1
    @3
    cU
    cnmcv
    fveq2
    @3
    cU
    cnsb
    fveq2
    coeq12d
    vu
    df-ims
    @0
    @1
    cU
    cnmcv
    fvex
    cU
    cnsb
    fvex
    coex
    fvmpt
    imsval.8
    cN
    @0
    cM
    @1
    imsval.6
    imsval.3
    coeq12i
    3eqtr4g
end
