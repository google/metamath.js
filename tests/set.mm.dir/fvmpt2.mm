include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cid.mm"
include "fvmpt2i.mm"
include "fvi.mm"
include "sylan9eq.mm"

theorem fvmpt2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y
  let cD: class D
  assume mptrcl.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint D y
  disjoint F y
  assert |- ( ( x e. A /\ B e. C ) -> ( F ` x ) = B )

  proof
    vx
    cv
    #
    cA
    wcel
    cB
    cC
    wcel
    @0
    cF
    cfv
    cB
    cid
    cfv
    cB
    vx
    cA
    cB
    cF
    mptrcl.1
    fvmpt2i
    cB
    cC
    fvi
    sylan9eq
end
