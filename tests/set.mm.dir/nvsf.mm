include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "nvvc.mm"
include "cpv.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcsm.mm"
include "syl.mm"

theorem nvsf
  let cS: class S
  let cU: class U
  let cX: class X
  assume nvsf.1: |- X = ( BaseSet ` U )
  assume nvsf.4: |- S = ( .sOLD ` U )


  assert |- ( U e. NrmCVec -> S : ( CC X. X ) --> X )

  proof
    cU
    cnv
    wcel
    cU
    c1st
    cfv
    #
    cvc
    wcel
    cc
    cX
    cxp
    cX
    cS
    wf
    cU
    @0
    @0
    eqid
    nvvc
    cS
    cU
    cpv
    cfv
    #
    @0
    cX
    cU
    @1
    @1
    eqid
    #
    vafval
    cS
    cU
    nvsf.4
    smfval
    cU
    @1
    cX
    nvsf.1
    @2
    bafval
    vcsm
    syl
end
