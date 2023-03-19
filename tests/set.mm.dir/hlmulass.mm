include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cc.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nvsass.mm"
include "sylan.mm"

theorem hlmulass
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cX: class X
  assume hlmulf.1: |- X = ( BaseSet ` U )
  assume hlmulf.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( ( A x. B ) S C ) = ( A S ( B S C ) ) )

  proof
    cU
    chlo
    wcel
    cU
    cnv
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
    hlnv
    cA
    cB
    cC
    cS
    cU
    cX
    hlmulf.1
    hlmulf.4
    nvsass
    sylan
end
