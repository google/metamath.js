include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "fvmptg.mm"
include "mpan2.mm"

theorem fvmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  assume fvmptg.1: |- ( x = A -> B = C )
  assume fvmptg.2: |- F = ( x e. D |-> B )
  assume fvmpt.3: |- C e. _V

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  assert |- ( A e. D -> ( F ` A ) = C )

  proof
    cA
    cD
    wcel
    cC
    cvv
    wcel
    cA
    cF
    cfv
    cC
    wceq
    fvmpt.3
    vx
    cA
    cB
    cC
    cD
    cvv
    cF
    fvmptg.1
    fvmptg.2
    fvmptg
    mpan2
end
