include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "mpteq2ia.mm"

theorem mpteq2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume mpteq2i.1: |- B = C


  assert |- ( x e. A |-> B ) = ( x e. A |-> C )

  proof
    vx
    cA
    cB
    cC
    cB
    cC
    wceq
    vx
    cv
    cA
    wcel
    mpteq2i.1
    a1i
    mpteq2ia
end
