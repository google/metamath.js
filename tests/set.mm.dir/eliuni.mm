include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "ciun.mm"
include "cv.mm"
include "wceq.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "eliun.mm"
include "sylibr.mm"

theorem eliuni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume eliuni.1: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint E x
  assert |- ( ( A e. D /\ E e. C ) -> E e. U_ x e. D B )

  proof
    cA
    cD
    wcel
    cE
    cC
    wcel
    #
    wa
    cE
    cB
    wcel
    #
    vx
    cD
    wrex
    cE
    vx
    cD
    cB
    ciun
    wcel
    @1
    @0
    vx
    cA
    cD
    vx
    cv
    cA
    wceq
    cB
    cC
    cE
    eliuni.1
    eleq2d
    rspcev
    vx
    cE
    cD
    cB
    eliun
    sylibr
end
