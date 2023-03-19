include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cmpt2.mm"
include "eqid.mm"
include "rgenw.mm"
include "jctr.mm"
include "ralrimivw.mm"
include "mpt2eq123.mm"
include "sylan2.mm"

theorem mpt2eq12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A = C /\ B = D ) -> ( x e. A , y e. B |-> E ) = ( x e. C , y e. D |-> E ) )

  proof
    cB
    cD
    wceq
    #
    cA
    cC
    wceq
    @0
    cE
    cE
    wceq
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cA
    wral
    vx
    vy
    cA
    cB
    cE
    cmpt2
    vx
    vy
    cC
    cD
    cE
    cmpt2
    wceq
    @0
    @3
    vx
    cA
    @0
    @2
    @1
    vy
    cB
    cE
    eqid
    rgenw
    jctr
    ralrimivw
    vx
    vy
    cA
    cB
    cE
    cC
    cD
    cE
    mpt2eq123
    sylan2
end
