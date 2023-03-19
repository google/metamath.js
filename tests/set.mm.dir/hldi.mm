include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cc.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nvdi.mm"
include "sylan.mm"

theorem hldi
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  assume hldi.1: |- X = ( BaseSet ` U )
  assume hldi.2: |- G = ( +v ` U )
  assume hldi.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) )

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
    hlnv
    cA
    cB
    cC
    cS
    cU
    cG
    cX
    hldi.1
    hldi.2
    hldi.4
    nvdi
    sylan
end
