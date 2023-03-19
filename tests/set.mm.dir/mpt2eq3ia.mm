include "cmpt2.mm"
include "wceq.mm"
include "wtru.mm"
include "cv.mm"
include "wcel.mm"
include "3adant1.mm"
include "mpt2eq3dva.mm"
include "trud.mm"

theorem mpt2eq3ia
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mpt2eq3ia.1: |- ( ( x e. A /\ y e. B ) -> C = D )


  assert |- ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D )

  proof
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    vy
    cA
    cB
    cD
    cmpt2
    wceq
    wtru
    vx
    vy
    cA
    cB
    cC
    cD
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    cC
    cD
    wceq
    wtru
    mpt2eq3ia.1
    3adant1
    mpt2eq3dva
    trud
end
