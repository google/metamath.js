include "chlo.mm"
include "wcel.mm"
include "ccphlo.mm"
include "cc.mm"
include "w3a.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "hlph.mm"
include "dipass.mm"
include "sylan.mm"

theorem hlipass
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cX: class X
  assume hlipass.1: |- X = ( BaseSet ` U )
  assume hlipass.4: |- S = ( .sOLD ` U )
  assume hlipass.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. CHilOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( ( A S B ) P C ) = ( A x. ( B P C ) ) )

  proof
    cU
    chlo
    wcel
    cU
    ccphlo
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
    cS
    co
    cC
    cP
    co
    cA
    cB
    cC
    cP
    co
    cmul
    co
    wceq
    cU
    hlph
    cA
    cB
    cC
    cP
    cS
    cU
    cX
    hlipass.1
    hlipass.4
    hlipass.7
    dipass
    sylan
end
