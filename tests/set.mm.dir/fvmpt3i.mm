include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "a1i.mm"
include "fvmpt3.mm"

theorem fvmpt3i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume fvmpt3.a: |- ( x = A -> B = C )
  assume fvmpt3.b: |- F = ( x e. D |-> B )
  assume fvmpt3i.c: |- B e. _V

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint V x
  assert |- ( A e. D -> ( F ` A ) = C )

  proof
    vx
    cA
    cB
    cC
    cD
    cF
    cvv
    fvmpt3.a
    fvmpt3.b
    cB
    cvv
    wcel
    vx
    cv
    cD
    wcel
    fvmpt3i.c
    a1i
    fvmpt3
end
