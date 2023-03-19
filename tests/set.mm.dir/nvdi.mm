include "cnv.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "cvc.mm"
include "cc.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "nvvc.mm"
include "vafval.mm"
include "smfval.mm"
include "bafval.mm"
include "vcdi.mm"
include "sylan.mm"

theorem nvdi
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


  assert |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) )

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
    cC
    cX
    wcel
    w3a
    cA
    cB
    cC
    cG
    co
    cS
    co
    cA
    cB
    cS
    co
    cA
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
    vcdi
    sylan
end
