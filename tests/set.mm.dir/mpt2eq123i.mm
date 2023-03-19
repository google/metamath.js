include "cmpt2.mm"
include "wceq.mm"
include "wtru.mm"
include "a1i.mm"
include "mpt2eq123dv.mm"
include "trud.mm"

theorem mpt2eq123i
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume mpt2eq123i.1: |- A = D
  assume mpt2eq123i.2: |- B = E
  assume mpt2eq123i.3: |- C = F


  assert |- ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F )

  proof
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vx
    vy
    cD
    cE
    cF
    cmpt2
    wceq
    wtru
    vx
    vy
    cA
    cB
    cC
    cD
    cE
    cF
    cA
    cD
    wceq
    wtru
    mpt2eq123i.1
    a1i
    cB
    cE
    wceq
    wtru
    mpt2eq123i.2
    a1i
    cC
    cF
    wceq
    wtru
    mpt2eq123i.3
    a1i
    mpt2eq123dv
    trud
end
