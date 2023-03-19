include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "cc.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcdir.mm"
include "sylan.mm"

theorem nvdir
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvdi.1: |- X = ( BaseSet ` U )
  assume nvdi.2: |- G = ( +v ` U )
  assume nvdi.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) )

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
    caddc
    co
    cC
    cS
    co
    cA
    cC
    cS
    co
    cB
    cC
    cS
    co
    cG
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
    cG
    @0
    cX
    cU
    cG
    nvdi.2
    vafval
    cS
    cU
    nvdi.4
    smfval
    cU
    cG
    cX
    nvdi.1
    nvdi.2
    bafval
    vcdir
    sylan
end
