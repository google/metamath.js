include "cmpt.mm"
include "wceq.mm"
include "wtru.mm"
include "a1i.mm"
include "mpteq12dv.mm"
include "trud.mm"

theorem mpteq12i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mpteq12i.1: |- A = C
  assume mpteq12i.2: |- B = D


  assert |- ( x e. A |-> B ) = ( x e. C |-> D )

  proof
    vx
    cA
    cB
    cmpt
    vx
    cC
    cD
    cmpt
    wceq
    wtru
    vx
    cA
    cB
    cC
    cD
    cA
    cC
    wceq
    wtru
    mpteq12i.1
    a1i
    cB
    cD
    wceq
    wtru
    mpteq12i.2
    a1i
    mpteq12dv
    trud
end
