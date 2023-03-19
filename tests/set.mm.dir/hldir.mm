include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cc.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nvdir.mm"
include "sylan.mm"

theorem hldir
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


  assert |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) )

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
    nvdir
    sylan
end
