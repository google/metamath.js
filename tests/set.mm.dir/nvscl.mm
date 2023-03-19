include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "cc.mm"
include "co.mm"
include "eqid.mm"
include "nvvc.mm"
include "cpv.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vccl.mm"
include "syl3an1.mm"

theorem nvscl
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cX: class X
  assume nvscl.1: |- X = ( BaseSet ` U )
  assume nvscl.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) -> ( A S B ) e. X )

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
    cc
    wcel
    cB
    cX
    wcel
    cA
    cB
    cS
    co
    cX
    wcel
    cU
    @0
    @0
    eqid
    nvvc
    cA
    cB
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
    vccl
    syl3an1
end
