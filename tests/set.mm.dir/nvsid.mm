include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "c1.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "cpv.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcidOLD.mm"
include "sylan.mm"

theorem nvsid
  let cA: class A
  let cS: class S
  let cU: class U
  let cX: class X
  assume nvscl.1: |- X = ( BaseSet ` U )
  assume nvscl.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( 1 S A ) = A )

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
    cA
    cX
    wcel
    c1
    cA
    cS
    co
    cA
    wceq
    cU
    @0
    @0
    eqid
    nvvc
    cA
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
    nvscl.4
    smfval
    cU
    @1
    cX
    nvscl.1
    @2
    bafval
    vcidOLD
    sylan
end
