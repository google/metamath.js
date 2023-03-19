include "wceq.mm"
include "wal.mm"
include "wral.mm"
include "cmpt.mm"
include "ax-5.mm"
include "mpteq12f.mm"
include "sylan.mm"

theorem mpteq12
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint C x
  assert |- ( ( A = C /\ A. x e. A B = D ) -> ( x e. A |-> B ) = ( x e. C |-> D ) )

  proof
    cA
    cC
    wceq
    #
    @0
    vx
    wal
    cB
    cD
    wceq
    vx
    cA
    wral
    vx
    cA
    cB
    cmpt
    vx
    cC
    cD
    cmpt
    wceq
    @0
    vx
    ax-5
    vx
    cA
    cB
    cC
    cD
    mpteq12f
    sylan
end
