include "wceq.mm"
include "wral.mm"
include "wdisj.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "ralimi.mm"
include "disjss2.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem disjeq2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A. x e. A B = C -> ( Disj_ x e. A B <-> Disj_ x e. A C ) )

  proof
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    wdisj
    #
    vx
    cA
    cC
    wdisj
    #
    @1
    cC
    cB
    wss
    #
    vx
    cA
    wral
    @2
    @3
    wi
    @0
    @4
    vx
    cA
    cC
    cB
    eqimss2
    ralimi
    vx
    cA
    cC
    cB
    disjss2
    syl
    @1
    cB
    cC
    wss
    #
    vx
    cA
    wral
    @3
    @2
    wi
    @0
    @5
    vx
    cA
    cB
    cC
    eqimss
    ralimi
    vx
    cA
    cB
    cC
    disjss2
    syl
    impbid
end
