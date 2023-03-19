include "cnv.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cnmcv.mm"
include "cfv.mm"
include "cnsb.mm"
include "ccom.mm"
include "eqid.mm"
include "nvf.mm"
include "nvmf.mm"
include "fco.mm"
include "syl2anc.mm"
include "imsval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem imsdf
  let cD: class D
  let cU: class U
  let cX: class X
  assume imsdfn.1: |- X = ( BaseSet ` U )
  assume imsdfn.8: |- D = ( IndMet ` U )


  assert |- ( U e. NrmCVec -> D : ( X X. X ) --> RR )

  proof
    cU
    cnv
    wcel
    #
    cX
    cX
    cxp
    #
    cr
    cD
    wf
    @1
    cr
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
    wf
    #
    @0
    cX
    cr
    @2
    wf
    @1
    cX
    @3
    wf
    @5
    cU
    @2
    cX
    imsdfn.1
    @2
    eqid
    #
    nvf
    cU
    @3
    cX
    imsdfn.1
    @3
    eqid
    #
    nvmf
    @1
    cX
    cr
    @2
    @3
    fco
    syl2anc
    @0
    @1
    cr
    cD
    @4
    cD
    cU
    @3
    @2
    @7
    @6
    imsdfn.8
    imsval
    feq1d
    mpbird
end
