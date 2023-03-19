include "wceq.mm"
include "wdisj.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "disjss1.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem disjeq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( A = B -> ( Disj_ x e. A C <-> Disj_ x e. B C ) )

  proof
    cA
    cB
    wceq
    #
    vx
    cA
    cC
    wdisj
    #
    vx
    cB
    cC
    wdisj
    #
    @0
    cB
    cA
    wss
    @1
    @2
    wi
    cB
    cA
    eqimss2
    vx
    cB
    cA
    cC
    disjss1
    syl
    @0
    cA
    cB
    wss
    @2
    @1
    wi
    cA
    cB
    eqimss
    vx
    cA
    cB
    cC
    disjss1
    syl
    impbid
end
