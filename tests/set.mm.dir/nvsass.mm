include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "cc.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "cpv.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcass.mm"
include "sylan.mm"

theorem nvsass
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cX: class X
  assume nvscl.1: |- X = ( BaseSet ` U )
  assume nvscl.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( ( A x. B ) S C ) = ( A S ( B S C ) ) )

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
    cc
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    cmul
    co
    cC
    cS
    co
    cA
    cB
    cC
    cS
    co
    cS
    co
    wceq
    cU
    @0
    @0
    eqid
    nvvc
    cA
    cB
    cC
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
    vcass
    sylan
end
