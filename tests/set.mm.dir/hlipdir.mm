include "chlo.mm"
include "wcel.mm"
include "ccphlo.mm"
include "w3a.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "hlph.mm"
include "dipdir.mm"
include "sylan.mm"

theorem hlipdir
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let cG: class G
  let cX: class X
  assume hlipdir.1: |- X = ( BaseSet ` U )
  assume hlipdir.2: |- G = ( +v ` U )
  assume hlipdir.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) P C ) = ( ( A P C ) + ( B P C ) ) )

  proof
    cU
    chlo
    wcel
    cU
    ccphlo
    wcel
    cA
    cX
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
    cG
    co
    cC
    cP
    co
    cA
    cC
    cP
    co
    cB
    cC
    cP
    co
    caddc
    co
    wceq
    cU
    hlph
    cA
    cB
    cC
    cP
    cU
    cG
    cX
    hlipdir.1
    hlipdir.2
    hlipdir.7
    dipdir
    sylan
end
