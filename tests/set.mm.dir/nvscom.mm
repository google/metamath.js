include "cnv.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "adantl.mm"
include "nvsass.mm"
include "3ancoma.mm"
include "sylan2b.mm"
include "3eqtr3d.mm"

theorem nvscom
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cX: class X
  assume nvscl.1: |- X = ( BaseSet ` U )
  assume nvscl.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( A S ( B S C ) ) = ( B S ( A S C ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    cA
    cB
    cmul
    co
    #
    cC
    cS
    co
    #
    cB
    cA
    cmul
    co
    #
    cC
    cS
    co
    #
    cA
    cB
    cC
    cS
    co
    cS
    co
    cB
    cA
    cC
    cS
    co
    cS
    co
    #
    @4
    @6
    @8
    wceq
    #
    @0
    @1
    @2
    @10
    @3
    @1
    @2
    wa
    @5
    @7
    cC
    cS
    cA
    cB
    mulcom
    oveq1d
    3adant3
    adantl
    cA
    cB
    cC
    cS
    cU
    cX
    nvscl.1
    nvscl.4
    nvsass
    @4
    @0
    @2
    @1
    @3
    w3a
    @8
    @9
    wceq
    @1
    @2
    @3
    3ancoma
    cB
    cA
    cC
    cS
    cU
    cX
    nvscl.1
    nvscl.4
    nvsass
    sylan2b
    3eqtr3d
end
